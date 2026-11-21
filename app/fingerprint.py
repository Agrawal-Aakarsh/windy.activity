"""Snapshot of sqlglot's import-time state: one short hash per module global, class attribute
and table entry. Comparing the pinned snapshot with a patched one shows exactly which pieces of
state an edit changes once everything is imported (including state derived from the edited line).

Items:  "mod:NAME"            module global
        "mod:NAME[key]"       entry of a module-level dict
        "mod:Class.attr"      class attribute (own __dict__ only)
        "mod:Class.attr[key]" entry of a class-level dict
        "mod:Class"           class shape (bases)
Function code is deliberately not hashed: edits inside function bodies are handled by line coverage."""
import enum
import functools
import hashlib
import importlib
import logging
import pkgutil
import re
import sys
import types

DEPTH = 7


def kr(k):
    if isinstance(k, str): return "s:" + k
    if isinstance(k, enum.Enum): return "e:" + type(k).__qualname__ + "." + k.name
    if isinstance(k, type): return "t:" + k.__module__ + "." + k.__qualname__
    if isinstance(k, (int, float, bool)) or k is None: return "c:" + repr(k)
    if isinstance(k, tuple): return "(" + ",".join(kr(x) for x in k) + ")"
    return "r:" + type(k).__name__


def canon(o, depth=DEPTH, seen=None):
    if o is None or isinstance(o, (bool, int, float, complex, str, bytes)):
        return repr(o)
    if isinstance(o, enum.Enum):
        return "E:" + type(o).__qualname__ + "." + o.name
    if isinstance(o, type):
        return "T:" + o.__module__ + "." + o.__qualname__
    if isinstance(o, types.ModuleType):
        return "M:" + o.__name__
    if depth <= 0:
        return "<" + type(o).__name__ + ">"
    seen = seen or ()
    if id(o) in seen:
        return "<cycle>"
    seen = seen + (id(o),)
    d = depth - 1
    if isinstance(o, dict):
        return "{" + ",".join(sorted(canon(k, d, seen) + ":" + canon(v, d, seen) for k, v in dict.items(o))) + "}"
    if isinstance(o, (list, tuple)):
        parts = [canon(x, d, seen) for x in o]
        if o and all(isinstance(x, type) for x in o):
            parts.sort()        # tuples of classes are often built from sets, whose order is not stable
        return ("[" if isinstance(o, list) else "(") + ",".join(parts) + "]"
    if isinstance(o, (set, frozenset)):
        return "S{" + ",".join(sorted(canon(x, d, seen) for x in o)) + "}"
    if isinstance(o, (types.FunctionType, types.LambdaType)):
        cells = []
        for c in o.__closure__ or ():
            try: cells.append(canon(c.cell_contents, d, seen))
            except ValueError: cells.append("<empty>")
        return "F:" + o.__module__ + "." + o.__qualname__ + "(" + canon(o.__defaults__, d, seen) + "|" + \
            canon(o.__kwdefaults__, d, seen) + "|" + ",".join(cells) + ")"
    if isinstance(o, (classmethod, staticmethod)):
        return "W:" + canon(o.__func__, d, seen)
    if isinstance(o, property):
        return "P:" + canon(o.fget, d, seen)
    if isinstance(o, functools.partial):
        return "PT:" + canon(o.func, d, seen) + canon(o.args, d, seen) + canon(o.keywords, d, seen)
    if isinstance(o, types.MethodType):
        return "BM:" + canon(o.__func__, d, seen) + "@" + canon(o.__self__, d, seen)
    if isinstance(o, (types.BuiltinFunctionType, types.MethodDescriptorType, types.WrapperDescriptorType,
                      types.MemberDescriptorType, types.GetSetDescriptorType)):
        return "B:" + getattr(o, "__qualname__", repr(o))
    if isinstance(o, logging.Logger):
        return "LOG:" + o.name
    if isinstance(o, re.Pattern):
        return "RE:" + repr(o.pattern) + str(o.flags)
    name = type(o).__module__ + "." + type(o).__qualname__
    if name.startswith("typing.") or type(o).__module__ in ("types", "typing", "collections.abc"):
        return "TY:" + re.sub(r" at 0x[0-9a-f]+", "", repr(o))
    state = {}
    if hasattr(o, "__dict__"):
        state.update(vars(o))
    for klass in type(o).__mro__:
        for s in getattr(klass, "__slots__", ()) if isinstance(getattr(klass, "__slots__", ()), (tuple, list)) else ():
            if hasattr(o, s) and s not in ("parent", "__weakref__", "__dict__"):
                try: state[s] = getattr(o, s)
                except Exception: pass
    if state:
        return "O:" + name + canon(state, d, seen)
    return "O:" + name + ":" + re.sub(r" at 0x[0-9a-f]+", "", repr(o))[:200]


def h(text):
    return hashlib.blake2b(text.encode("utf-8", "replace"), digest_size=6).hexdigest()


def classes_of(m):
    seen, out = set(), []
    def rec(c):
        if id(c) in seen: return
        seen.add(id(c)); out.append(c)
        for v in list(vars(c).values()):
            if isinstance(v, type) and v.__module__ == c.__module__ and v.__qualname__.startswith(c.__qualname__ + "."):
                rec(v)
    for v in list(vars(m).values()):
        if isinstance(v, type) and v.__module__ == m.__name__:
            rec(v)
    return out


SKIP_ATTRS = {"__module__", "__qualname__", "__doc__", "__dict__", "__weakref__", "__annotations__", "__firstlineno__",
              "__static_attributes__", "__parameters__", "__orig_bases__", "__slots__", "__match_args__", "__annotate__",
              "__annotations_cache__", "__abstractmethods__", "_abc_impl"}


def snapshot(modnames):
    out = {}
    for mn in modnames:
        m = sys.modules.get(mn)
        if m is None:
            continue
        for name, v in list(vars(m).items()):
            if name.startswith("__") or isinstance(v, types.ModuleType):
                continue
            if isinstance(v, type) and v.__module__ == mn:
                continue
            key = mn + ":" + name
            try:
                if type(v) is dict:
                    out[key] = h("dict")
                    for k, x in dict.items(v):
                        out[key + "[" + kr(k) + "]"] = h(canon(x))
                else:
                    out[key] = h(canon(v))
            except Exception as e:
                out[key] = "err:" + type(e).__name__
        for c in classes_of(m):
            ck = mn + ":" + c.__qualname__
            out[ck] = h(",".join(b.__module__ + "." + b.__qualname__ for b in c.__mro__))
            if issubclass(c, enum.Enum):
                out[ck + ".<members>"] = h(",".join(sorted(x.name + "=" + canon(x.value) for x in c)))
                continue
            for name, v in list(vars(c).items()):
                if name in SKIP_ATTRS or (isinstance(v, type) and v.__module__ == mn and v.__qualname__.startswith(c.__qualname__ + ".")):
                    continue
                key = ck + "." + name
                try:
                    if type(v) is dict:
                        out[key] = h("dict")
                        for k, x in dict.items(v):
                            out[key + "[" + kr(k) + "]"] = h(canon(x))
                    else:
                        out[key] = h(canon(v))
                except Exception as e:
                    out[key] = "err:" + type(e).__name__
    return out


def load_all(failed=None):
    """Import every sqlglot module. With a list for `failed`, modules that cannot be imported are
    recorded there instead of raising (the top-level package itself must still import)."""
    import sqlglot
    names = ["sqlglot"]
    for info in pkgutil.walk_packages(sqlglot.__path__, prefix="sqlglot.", onerror=lambda n: failed.append(n) if failed is not None else None):
        if info.name == "sqlglot.__main__":
            continue
        try:
            importlib.import_module(info.name)
            names.append(info.name)
        except BaseException:
            if failed is None:
                raise
            failed.append(info.name)
    return names


if __name__ == "__main__":
    import json
    sys.path.insert(0, sys.argv[1])
    sys.dont_write_bytecode = True
    names = load_all()
    snap = snapshot(names)
    json.dump({"modules": names, "snap": snap}, open(sys.argv[2], "w"))
    print("modules", len(names), "items", len(snap), file=sys.stderr)
