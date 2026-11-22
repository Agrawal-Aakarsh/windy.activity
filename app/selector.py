"""Blast Radius selector.

For every patch, pick the tests that the change can reach, using maps built once from the
pinned sqlglot commit (see build_map.py): per-test line coverage, files each test opens,
which tests use which classes, and static name references. Nothing here is keyed on a
specific patch or on a kind of edit; every rule is "which tests can observe this line".
"""
import ast
import copy
import json
import os
import pickle
import re
import sys
import time
import zlib
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

DATA = Path(os.environ.get("BR_DATA", "/data"))
SG = Path(os.environ.get("BR_SG", "/sqlglot"))
MAP = os.environ.get("BR_MAP", str(Path(__file__).with_name("map.pkl.z")))
FAMILY_DIRS = ("sqlglot/dialects/", "sqlglot/parsers/", "sqlglot/generators/", "sqlglot/typing/")
CORE_BASENAMES = ("dialect.py", "__init__.py")
GLOBAL_CONFIG = ("pyproject.toml", "setup.cfg", "setup.py", "pytest.ini", "tox.ini", "conftest.py")


T0 = time.time()


LOGBUF = []


def log(*a):
    if TELEM:
        LOGBUF.append(" ".join(map(str, a)))
    print(*a, file=sys.stderr)


TELEM2 = os.environ.get("BR_TELEM2", "0") == "1"                  # DIAGNOSTIC ONLY (see telemetry_wide() below)
TELEM = os.environ.get("BR_TELEM", "0") == "1"                    # DIAGNOSTIC ONLY (see telemetry() below)


# ---------------------------------------------------------------- patch parsing
class FilePatch:
    def __init__(self):
        self.old = self.new = None
        self.binary = False
        self.hunks = []          # (old_start, [(tag, text)])

    @property
    def removed(self):
        out = []
        for start, body in self.hunks:
            o = start
            for tag, _ in body:
                if tag == "-":
                    out.append(o)
                if tag != "+":
                    o += 1
        return out

    @property
    def insert_points(self):
        """Old line numbers in front of which pure additions land."""
        out = []
        for start, body in self.hunks:
            o = start
            prev = " "
            for tag, _ in body:
                if tag == "+" and prev != "-" :
                    out.append(o)
                if tag != "+":
                    o += 1
                if tag != "+" or prev != "-":
                    prev = tag
        return out

    def added_text(self):
        return [t for _, b in self.hunks for tag, t in b if tag == "+"]

    def removed_text(self):
        return [t for _, b in self.hunks for tag, t in b if tag == "-"]

    def apply(self, old_src):
        old = old_src.split("\n")
        out, pos = [], 0
        for start, body in self.hunks:
            i = max(start - 1, 0)
            out.extend(old[pos:i])
            pos = i
            for tag, text in body:
                if tag == " ":
                    out.append(old[pos] if pos < len(old) else text); pos += 1
                elif tag == "-":
                    pos += 1
                else:
                    out.append(text)
        out.extend(old[pos:])
        return "\n".join(out)


def parse_patch(text):
    files, cur, body = [], None, None
    for line in text.split("\n"):
        if line.startswith("diff --git"):
            cur = FilePatch(); files.append(cur); body = None
            m = re.match(r"diff --git a/(.+) b/(.+)$", line)
            if m:                                 # kept when there are no ---/+++ lines (binary patches)
                cur.old, cur.new = m.group(1), m.group(2)
        elif cur is not None and line.startswith("new file mode"):
            cur.old = None
        elif cur is not None and line.startswith("deleted file mode"):
            cur.new = None
        elif cur is not None and (line.startswith("GIT binary patch") or line.startswith("Binary files")):
            cur.binary = True
        elif cur is None:
            continue
        elif line.startswith("--- ") and body is None:
            p = line[4:].strip(); cur.old = None if p == "/dev/null" else p[2:] if p[:2] in ("a/", "b/") else p
        elif line.startswith("+++ ") and body is None:
            p = line[4:].strip(); cur.new = None if p == "/dev/null" else p[2:] if p[:2] in ("a/", "b/") else p
        elif line.startswith("rename from "):
            cur.old = line[12:].strip()
        elif line.startswith("rename to "):
            cur.new = line[10:].strip()
        elif line.startswith("@@"):
            start = int(line.split("-", 1)[1].split(",")[0].split(" ")[0])
            body = []; cur.hunks.append((start, body))
        elif body is not None and line[:1] in (" ", "-", "+"):
            body.append((line[0], line[1:]))
        elif body is not None and line == "":
            body.append((" ", ""))
    for f in files:
        for _, b in f.hunks:
            while b and b[-1] == (" ", ""):
                b.pop()
    return files


# ---------------------------------------------------------------- selector
class Selector:
    def __init__(self, m, tests):
        self.m = m
        num = {t["id"]: t["number"] for t in tests}
        self.all = set(num.values())
        self.tr = [num.get(i) for i in m["ids"]]            # map index -> test number (None if absent)
        self.by_file = {}
        for t in tests:
            self.by_file.setdefault(t["file"], set()).add(t["number"])
        self.id_num = num
        self.unknown = self.all - {n for n in self.tr if n is not None}
        self.lines, self.imp = m["lines"], {f: set(v) for f, v in m["import_lines"].items()}
        self.struct, self.refs, self.used = m["struct"], m["refs"], m["used"]
        self.modfile = {v["module"]: f for f, v in m["struct"].items()}
        self.rev = {n: i for i, n in enumerate(self.tr) if n is not None}     # test number -> map index
        self.touched, self.line_only = [], True
        self.texts, self.name_cache, self.pending = None, {}, []

    def T(self, idxs):
        return {self.tr[i] for i in idxs if self.tr[i] is not None}

    def cov(self, f, lo, hi):
        d = self.lines.get(f, {})
        out = set()
        for l in range(lo, hi + 1):
            if l in d:
                out.update(d[l])
        return self.T(out)

    def scope(self, f, line):
        best = None
        for s in self.struct[f]["scopes"]:
            if s[0] <= line <= s[1] and (best is None or s[1] - s[0] <= best[1] - best[0]):
                best = s
        return best

    def stmt(self, f, line):
        best = None
        for s in self.struct[f]["stmts"]:
            if s[0] <= line <= s[1] and (best is None or s[1] - s[0] < best[1] - best[0]):
                best = s
        return best

    # ---- fallbacks
    def fallback(self, f):
        base = os.path.basename(f)
        if f.startswith(FAMILY_DIRS) and base not in CORE_BASENAMES:
            out = set()
            for d in FAMILY_DIRS:
                g = d + base
                if g in self.struct:
                    out |= self.cov(g, 1, self.struct[g]["nlines"])
                    for s in self.struct[g]["scopes"]:
                        if s[2] == "class":
                            out |= self.T(self.used.get(s[3], ()))
            return out | self.unknown
        return set(self.all)

    def users(self, owner, f):
        if owner is not None and owner in self.used:
            return self.T(self.used[owner])
        if owner is not None and f.startswith("sqlglot/expressions/"):
            return set()                       # expression class no test ever instantiates
        return self.fallback(f)

    def by_names(self, names, owner, f):
        out = set()
        for nm in names:
            derived, rt = False, set()
            for rf, rl in self.refs.get(nm, ()):
                sc, st = self.scope(rf, rl), self.stmt(rf, rl)
                lo, hi = (st[0], st[1]) if st else (rl, rl)
                if sc is not None and sc[2] in ("func", "lambda"):
                    rt |= self.cov(rf, lo, hi)
                    if sc[2] == "func" and any(l in self.imp.get(rf, ()) for l in range(lo, hi + 1)):
                        derived = True         # read while importing: value is baked into other state
                elif st is not None and nm in st[2]:
                    continue                    # the definition itself, or a same-name extension in a subclass
                else:
                    derived = True              # read at class/module level under another name
            users = self.users(owner, f)
            out |= users if derived else (rt & users)
        return out

    # ---- one changed line of a sqlglot source file
    # returns (tests that can reach the line at run time, static answer for import-time effects or None)
    def code_line(self, f, line):
        sc, st = self.scope(f, line), self.stmt(f, line)
        if sc is not None and sc[2] in ("func", "lambda"):
            if sc[2] == "lambda":
                self.touched.append((f, sc[0], sc[1]))
                return self.cov(f, sc[0], sc[1]), None
            if line < sc[4] or st is None or not (sc[0] <= st[0] and st[1] <= sc[1]):
                lo, hi = sc[4], sc[1]          # signature, decorator or a line between statements
            else:
                lo, hi = st[0], st[1]
            self.touched.append((f, lo, hi))
            out = self.cov(f, lo, hi)
            if line < sc[4] or any(l in self.imp.get(f, ()) for l in range(lo, hi + 1)):
                return out, ("import", self.fallback(f))   # this code (or its signature) takes effect while importing
            return out, None
        owner = sc[3] if sc is not None else None
        if st is not None and st[2]:
            return set(), ("level", self.by_names(st[2], owner, f))
        return set(), ("level", self.users(owner, f) if owner else self.fallback(f))

    def source_file(self, fp):
        f = fp.old
        if fp.binary:
            return set(self.all)
        if fp.old is None:
            # a new module: harmless unless importing the package now fails or something enumerates modules
            self.pending.append(("module", set(self.all)))
            return self.mentions_any(("pkgutil", "walk_packages", "iter_modules", "listdir", "glob("))
        if fp.new is None or fp.old != fp.new or f not in self.struct:
            # a module went away (deleted or renamed): everything that uses it, plus whatever the import-state diff shows
            self.pending.append(("module", set(self.all)))
            out = set()
            if f in self.struct:
                out |= self.cov(f, 1, self.struct[f]["nlines"])
                for sc in self.struct[f]["scopes"]:
                    if sc[2] == "class":
                        out |= self.T(self.used.get(sc[3], ()))
                out |= self.mentions_any((self.struct[f]["module"], os.path.basename(f)[:-3]))
            else:
                out = set(self.all)
            return out
        old_src = (SG / f).read_text(encoding="utf-8")
        new_src = fp.apply(old_src)
        try:
            new_tree = parse_src(new_src)
        except SyntaxError:
            # the module can no longer be imported: its users for sure, and the import check decides the rest
            self.pending.append(("module", set(self.all)))
            out = self.cov(f, 1, self.struct[f]["nlines"]) | self.mentions_any((self.struct[f]["module"], os.path.basename(f)[:-3]))
            for sc in self.struct[f]["scopes"]:
                if sc[2] == "class":
                    out |= self.T(self.used.get(sc[3], ()))
            return out
        squash = lambda lines: re.sub(r"\s+", "", "".join(l.split("#")[0] for l in lines))
        if squash(fp.removed_text()) == squash(fp.added_text()):
            # only comments, blank lines or layout differ on the face of it: confirm on the syntax trees
            import cond
            if cond._diff(parse_src(old_src), new_tree, set(fp.removed) | set(fp.insert_points)) is None:
                return set()                    # identical program
        if NOOP:
            try:
                if same_program_at(fp, parse_src(old_src), new_tree, f):
                    log("same-code", f)
                    return set()                # every changed function still compiles to the same instructions
            except Exception:
                pass
        out = set()
        nlines = self.struct[f]["nlines"]
        targets = set(fp.removed)
        for p in fp.insert_points:
            targets.update(x for x in (p - 1, p) if 1 <= x <= nlines)
        for line in targets:
            run, static = self.code_line(f, line)
            out |= run
            if static is not None:
                self.pending.append(static)
        return out

    def test_file(self, fp):
        f = fp.old or fp.new
        todo, seen = [f], {f}
        while todo:                                  # test modules that import this one, transitively
            x = todo.pop()
            for g, deps in self.m["test_imports"].items():
                if x in deps and g not in seen:
                    seen.add(g); todo.append(g)
        whole = set()
        for g in seen:
            whole |= self.by_file.get(g, set())
        if fp.old is None:
            # a new module under tests/: its own tests are not numbered; a conftest or package file affects everyone
            return set(self.all) if os.path.basename(f) in ("conftest.py", "__init__.py") else set()
        if fp.new is None or fp.old != fp.new or f not in self.m["test_spans"] or fp.binary:
            return whole
        old_src = (SG / f).read_text(encoding="utf-8")
        try:
            old_tree, new_tree = parse_src(old_src), parse_src(fp.apply(old_src))
        except SyntaxError:
            return whole
        if ast.dump(old_tree) == ast.dump(new_tree):
            return set()

        def shape(tree):
            rest, classes = [], {}
            for node in tree.body:
                if isinstance(node, ast.ClassDef):
                    methods, other = {}, [ast.dump(b) for b in node.bases] + [ast.dump(d) for d in node.decorator_list]
                    for x in node.body:
                        if isinstance(x, (ast.FunctionDef, ast.AsyncFunctionDef)):
                            methods[x.name] = ast.dump(x)
                        else:
                            other.append(ast.dump(x))
                    classes[node.name] = (methods, other)
                else:
                    rest.append(ast.dump(node))
            return rest, classes

        (rest_a, cls_a), (rest_b, cls_b) = shape(old_tree), shape(new_tree)
        if rest_a != rest_b or set(cls_a) != set(cls_b) or len(seen) > 1:
            return whole                             # module-level change, or other test modules build on this one
        out = set()
        for cname in cls_a:
            (ma, oa), (mb, ob) = cls_a[cname], cls_b[cname]
            if oa != ob:
                return whole                         # class-level statements, bases or decorators changed
            changed = [n for n in set(ma) | set(mb) if ma.get(n) != mb.get(n)]
            if not changed:
                continue
            if any(cname in o for k, (_, other) in cls_a.items() if k != cname for o in other):
                return whole                         # another class in the file derives from this one
            for name in changed:
                if not name.startswith("test"):
                    return whole                     # a helper or setUp/tearDown: every test here may depend on it
                tid = f"{f}::{cname}::{name}"
                if tid in self.id_num:               # a brand new test method has no number, so nothing to run
                    out.add(self.id_num[tid])
        return out

    # ---- tests that read a piece of import-time state (items come from fingerprint.py)
    def name_tests(self, name):
        if self.texts is None:
            self.texts = {f: (SG / f).read_text(encoding="utf-8").split("\n") for f in self.struct if f.startswith("sqlglot/")}
        if name not in self.name_cache:
            pat, out = re.compile(r"(?<![A-Za-z0-9_])" + re.escape(name) + r"(?![A-Za-z0-9_])"), set()
            for f, lines in self.texts.items():
                for i, l in enumerate(lines, 1):
                    if name in l and pat.search(l):
                        st = self.stmt(f, i)
                        out |= self.cov(f, st[0], st[1]) if st else self.cov(f, i, i)
            self.name_cache[name] = out
        return self.name_cache[name]

    def readers(self, items, gone=()):
        out = set()
        for it in items:
            mod, rest = it.split(":", 1)
            if mod in gone:
                continue                         # the module itself was removed; its users are selected directly
            f = self.modfile.get(mod)
            if f is None:
                continue                         # state of a module that is new in this patch: nothing reads it yet
            key = None
            if rest.endswith("]") and "[" in rest:
                i = rest.index("["); rest, key = rest[:i], rest[i + 1:-1]
            binding = mod + ":" + rest
            if key is not None and binding in self.m["aliases"]:
                ku = self.m["keyuse"].get(self.m["aliases"][binding], {})
                out |= self.T(ku.get(key, ())) | self.T(ku.get("*", ()))
                continue
            scopes = {sc[3]: sc for sc in self.struct[f]["scopes"]}
            if binding in scopes and scopes[binding][2] == "class":
                out |= self.users(binding, f)          # the class itself changed shape
                continue
            if binding in scopes:                      # a function whose defaults or closure changed
                out |= self.cov(f, scopes[binding][0], scopes[binding][1])
            cls, _, name = rest.rpartition(".")
            if name == "<members>":
                out |= self.fallback(f)
                continue
            rt = self.name_tests(name)
            owner = mod + ":" + cls
            out |= (rt & self.T(self.used[owner])) if cls and owner in self.used else rt
        return out

    _last = None

    def select(self, text):
        """Returns (tests reachable at run time, [static answers for import-time effects])."""
        if self._last is not None and self._last[0] == text:      # asked again for the same patch text
            _, out, pending, touched, line_only = self._last
            self.pending, self.touched, self.line_only = [(m, set(p)) for m, p in pending], list(touched), line_only
            return set(out), self.pending
        self.pending, self.touched, self.line_only = [], [], True
        out = self._select(text)
        if self.pending:
            self.line_only = False            # some candidates come from import-time state, not from executed lines
        self._last = (text, set(out), [(m, set(p)) for m, p in self.pending], list(self.touched), self.line_only)
        return out, self.pending

    def _select(self, text):
        out = set()
        for fp in parse_patch(text):
            f = fp.old or fp.new
            if f is None:
                continue
            if not (f.startswith("sqlglot/") and f.endswith(".py")):
                self.line_only = False        # candidates that do not come from executed source lines
            if os.path.basename(f) in ("conftest.py", "pytest.ini", "tox.ini"):
                out |= self.all
            elif f in GLOBAL_CONFIG:
                # packaging/config files: they matter to every test only if they configure pytest
                try:
                    new_text = fp.apply((SG / f).read_text(encoding="utf-8")) if fp.old and fp.new and not fp.binary else None
                except OSError:
                    new_text = None
                old_text = (SG / f).read_text(encoding="utf-8") if (SG / f).exists() else ""
                if new_text is None or "pytest" in new_text.lower() or "pytest" in old_text.lower():
                    out |= self.all
                else:
                    out |= self.T(self.m["opened"].get(f, ())) | self.mentions_any((f, f.rsplit(".", 1)[0]) if f != "setup.py" else (f,))
            elif f.startswith("sqlglot/") and f.endswith(".py"):
                out |= self.source_file(fp)
            elif f.startswith("tests/") and f.endswith(".py"):
                out |= self.test_file(fp)
            else:
                if f.endswith(".sql") and fp.old == fp.new and (SG / f).exists():
                    # tests/helpers.py drops blank lines and lines starting with "--" before using a fixture
                    keep = lambda s: [l for l in s.splitlines() if l and not l.startswith("--")]
                    old_src = (SG / f).read_text(encoding="utf-8")
                    if keep(old_src) == keep(fp.apply(old_src)):
                        continue
                got = self.T(self.m["opened"].get(f, ()))
                if not got and f.endswith(".py"):
                    got = self.mentions(f)
                if fp.binary and not got and f.startswith("tests/"):
                    got = set(self.all)
                out |= got
        return out

    def mentions_any(self, keys):
        out = set()
        for tf in self.m["test_spans"]:
            try:
                text = (SG / tf).read_text(encoding="utf-8")
            except OSError:
                continue
            if any(k in text for k in keys):
                out |= self.by_file.get(tf, set())
        return out

    def mentions(self, f):
        """A Python file outside sqlglot/ and tests/ (build scripts and the like): tests whose module mentions it."""
        keys = {f.split("/")[0], os.path.basename(f)[:-3]} - {"setup", "__init__", ""}
        out = set()
        for tf in self.m["test_spans"]:
            try:
                text = (SG / tf).read_text(encoding="utf-8")
            except OSError:
                continue
            if any(k in text for k in keys):
                out |= self.by_file.get(tf, set())
        return out


def pack(nums, ms, spare=()):
    """Split the chosen tests over 1..8 workers at the lowest cost. `spare` are tests that were candidates but got
    ruled out: they are added back wherever they fit without raising the busiest worker, which costs nothing."""
    if not nums:
        return []
    order = sorted(nums, key=lambda n: -ms[n])
    best = None
    for k in range(1, 9):
        loads, workers = [0] * k, [[] for _ in range(k)]
        for n in order:
            i = loads.index(min(loads)); workers[i].append(n); loads[i] += ms[n]
        cost = max(loads) + 2000 * k
        if best is None or cost < best[0]:
            best = (cost, workers, loads)
    workers, loads = best[1], best[2]
    keep = [i for i, w in enumerate(workers) if w]
    workers, loads = [workers[i] for i in keep], [loads[i] for i in keep]
    if FILL and spare:
        top = max(loads) - 2                      # stay strictly under the busiest worker (ms)
        for n in sorted(set(spare) - set(nums), key=lambda n: ms[n]):
            i = loads.index(min(loads))
            if loads[i] + ms[n] > top and ms[n] > 0:
                break                             # sorted by time: nothing later fits either
            workers[i].append(n); loads[i] += ms[n]
    return workers


PIN = os.environ.get("BR_PIN", str(Path(__file__).with_name("unstable.json")))   # state items whose value varies run to run
STATE = os.environ.get("BR_STATE", "1") == "1"                    # import-state diff for import-time edits
NARROW_IMPORT = os.environ.get("BR_NARROW_IMPORT", "0") == "1"    # when only dialect modules fail to import, select their users
STATE_EMPTY_KEEPS_STATIC = os.environ.get("BR_STATE_EMPTY", "1") == "1"
VERIFY = os.environ.get("BR_VERIFY", "1") == "1"
VERIFY_RATIO = float(os.environ.get("BR_VERIFY_RATIO", "0.45"))   # run for real only if est. CPU <= ratio * simulated cost
VERIFY_RATIO_HEAVY = float(os.environ.get("BR_VERIFY_RATIO_HEAVY", "0.65"))
HEAVY_SECS = 3.0
SKIP_HEAVY = os.environ.get("BR_SKIP_HEAVY", "0") == "1"          # drop heavy tests when every other candidate passes
SLOW_FILES = ("tests/test_optimizer.py", "tests/test_executor.py")
EQUIV = os.environ.get("BR_EQUIV", "0") == "1"                    # side-by-side check of a swapped comparison operator
EQUIV_CONST = os.environ.get("BR_EQUIV_CONST", "0") == "1"        # literal operand: do not vary that side in the probe
EQUIV_BUDGET = float(os.environ.get("BR_EQUIV_BUDGET", "2.0"))    # CPU seconds of cheap candidates to observe
EQUIV_MAX_TESTS = int(os.environ.get("BR_EQUIV_MAX_TESTS", "12"))
EQUIV_PER_CLASS = int(os.environ.get("BR_EQUIV_PER_CLASS", "4"))
EQUIV_MIN_RUNS = int(os.environ.get("BR_EQUIV_MIN_RUNS", "20"))
EQUIV_MIN_TESTS = int(os.environ.get("BR_EQUIV_MIN_TESTS", "3"))
SLICE = os.environ.get("BR_SLICE", "1") == "1"                    # run fixture-driven proxies only on the records that reach the change
FIXSLICE = os.environ.get("BR_FIXSLICE", "0") == "1"              # fixture-only patches: run candidates on the changed records only
DROP_HEAVY = os.environ.get("BR_DROP_HEAVY", "0") == "1"          # diagnostic, see main()
TASTE = os.environ.get("BR_TASTE", "1") == "1"                    # sample a few records of a proxy before running all of it
TASTE_N = int(os.environ.get("BR_TASTE_N", "10"))
TASTE_MIN = int(os.environ.get("BR_TASTE_MIN", "30"))
TASTE_STOP = int(os.environ.get("BR_TASTE_STOP", "3"))
OPT = os.environ.get("BR_OPT", "0") == "1"                        # compare optimizer-step output with the pinned commit's
OPT_RATIO = float(os.environ.get("BR_OPT_RATIO", "0.5"))
SELF = os.environ.get("BR_SELF", "0") == "1"                      # run a record-looping heavy test on the records that reach the change
SELF_RATIO = float(os.environ.get("BR_SELF_RATIO", "0.5"))
SELF_FIRST = int(os.environ.get("BR_SELF_FIRST", "6"))
WIDE_PROBE = os.environ.get("BR_WIDE_PROBE", "0") == "1"          # run the comparison probe even when most tests are selected
FLAGS = os.environ.get("BR_FLAGS", "0") == "1"                    # class-level true/false settings: recorded users (flags.pkl.z)
NOOP = os.environ.get("BR_NOOP", "0") == "1"                      # edits whose functions compile to identical code select nothing
FILL = os.environ.get("BR_FILL", "0") == "1"                      # put ruled-out candidates into free worker time
COND = os.environ.get("BR_COND", "0") == "1"                      # use recorded condition values (cond.pkl.z)
MULTI = os.environ.get("BR_MULTI", "0") == "1"                    # check multi-file commits one file at a time
HEAVYRUN = os.environ.get("BR_HEAVYRUN", "0") == "1"              # run expensive tests for real when that is cheap
HEAVYRUN_RATIO = float(os.environ.get("BR_HEAVYRUN_RATIO", "0.5"))
REFINE_RATIO = float(os.environ.get("BR_REFINE_RATIO", "0.6"))
REFINE_MAX = int(os.environ.get("BR_REFINE_MAX", "26"))           # more changed records than this: keep the heavy test
REFINE = os.environ.get("BR_REFINE", "0") == "1"                  # proxy failed: run the heavy test on the changed records only
PROXY = os.environ.get("BR_PROXY", "0") == "1"
PROXY_SIM = float(os.environ.get("BR_PROXY_SIM", "0.6"))


def cost_ms(nums, ms):
    w = pack(nums, ms)
    return max(sum(ms[n] for n in x) for x in w) + 2000 * len(w) if w else 0


def _pure(node):
    """An expression that can be evaluated a second time without side effects (no calls)."""
    if isinstance(node, (ast.Name, ast.Constant)):
        return True
    if isinstance(node, ast.Attribute):
        return _pure(node.value)
    if isinstance(node, ast.Subscript):
        return _pure(node.value) and _pure(node.slice)
    if isinstance(node, ast.Tuple):
        return all(_pure(e) for e in node.elts)
    if isinstance(node, ast.UnaryOp):
        return _pure(node.operand)
    return False


def compare_swap(old_src, new_src):
    """If the only difference between two versions of a module is the operator of one two-operand comparison whose
    operands are plain names/attributes/constants, describe it; otherwise None."""
    try:
        a, b = parse_src(old_src), parse_src(new_src)
    except SyntaxError:
        return None
    found = []

    def walk(x, y):
        if len(found) > 1:
            return
        if type(x) is not type(y):
            found.append(None); return
        if isinstance(x, ast.Compare) and len(x.ops) == 1 and len(y.ops) == 1 and type(x.ops[0]) is not type(y.ops[0]) \
                and ast.dump(x.left) == ast.dump(y.left) and ast.dump(x.comparators[0]) == ast.dump(y.comparators[0]):
            found.append((x, y)); return
        for (_, va), (_, vb) in zip(ast.iter_fields(x), ast.iter_fields(y)):
            if isinstance(va, ast.AST) and isinstance(vb, ast.AST):
                walk(va, vb)
            elif isinstance(va, list) and isinstance(vb, list):
                if len(va) != len(vb):
                    found.append(None); return
                for p, q in zip(va, vb):
                    if isinstance(p, ast.AST) and isinstance(q, ast.AST):
                        walk(p, q)
                    elif p != q:
                        found.append(None); return
            elif va != vb:
                found.append(None); return

    walk(a, b)
    if len(found) != 1 or found[0] is None:
        return None
    x, y = found[0]
    if not (_pure(x.left) and _pure(x.comparators[0])):
        return None
    out = {"line": y.lineno, "left": ast.unparse(y.left), "right": ast.unparse(y.comparators[0]),
           "old": type(x.ops[0]).__name__, "new": type(y.ops[0]).__name__}
    if EQUIV_CONST and isinstance(y.comparators[0], ast.Constant):
        out["const"] = "right"
    elif EQUIV_CONST and isinstance(y.left, ast.Constant):
        out["const"] = "left"
    return out


class Checker:
    """Runs the cheap candidates for real against the patched source. Only ever removes tests
    when every one of them is reported as passed; any doubt keeps the full static selection."""
    def __init__(self, tests, ms):
        self.ms, self.v = ms, None
        self.id = {t["number"]: t["id"] for t in tests}
        self.file = {t["number"]: t["file"] for t in tests}
        self.cpu = 0.0
        self.proxy, self.cpu_own, self.cpu_setup, self.base_sets = {}, {}, {}, {}
        self.deadline = time.time() + 100

    def start(self):
        if self.v is None:
            from verify import Verifier
            self.v = Verifier(SG, os.environ.get("BR_TMP", "/tmp/br_wc"), PIN)
        self.v.extra = self.extra          # the rest of a multi-file commit, applied in every real run
        return self.v

    def patched(self, text):
        out = {}
        for fp in parse_patch(text):
            if fp.binary or (fp.old is not None and not (SG / fp.old).exists()):
                return None
            old_src = (SG / fp.old).read_text(encoding="utf-8") if fp.old else ""
            if fp.old and fp.old != fp.new:
                out[fp.old] = None               # deleted, or the old name of a rename
            if fp.new:
                out[fp.new] = fp.apply(old_src)
        return out

    def resolve(self, name, text, sel, chosen, pending):
        """Edits that take effect while sqlglot is imported: import the patched package once and
        see which pieces of import-time state actually changed, then select the tests that read them."""
        self.state_clean = False
        static = set().union(*[p for _, p in pending])
        patched = self.patched(text) if STATE else None
        if patched is None or self.left() < 15:
            # cannot look at the import-time effect: only the whole suite is safe
            return set(sel.all) if STATE else chosen | static
        first = self.v is None or not self.v.baseline
        self.n_state += 1
        r = self.start().state(patched, limit=min(25.0, self.left() - 5))
        self.cpu += self.v.last.get("cpu", 0) + (self.v.base_cpu if first else 0)
        if os.environ.get("BR_DEBUG"):
            log("state-cpu", name, self.v.last.get("cpu"), "base", self.v.base_cpu if first else 0)
        if r is None or r["n"] > 300:
            log("state", name, "import failed" if r is None else "many items", "-> all tests")
            return set(sel.all)
        if r.get("failed_modules"):
            # some modules no longer import. If they are all dialect-family modules (loaded lazily), only the tests
            # that use those dialects are affected; a core module failing takes everything with it.
            files = [sel.modfile.get(m) for m in r["failed_modules"]]
            if not NARROW_IMPORT or any(f is None or not f.startswith(FAMILY_DIRS) or os.path.basename(f) in CORE_BASENAMES for f in files):
                log("state", name, "modules fail to import", r["failed_modules"][:3], "-> all tests")
                return set(sel.all)
            for f in files:
                chosen = chosen | sel.fallback(f) | sel.mentions_any((os.path.basename(f)[:-3],))
            log("state", name, "dialect modules fail to import", r["failed_modules"][:4], "->", len(chosen))
        if r["n"] == 0:
            # nothing observable changed at import time. A class/module-level edit that leaves no trace is
            # unusual, so those keep their static answer; import-time function lines add nothing.
            extra = set().union(*[p for mode, p in pending if mode == "level"]) if STATE_EMPTY_KEEPS_STATIC else set()
            log("state", name, "no change", len(extra))
            self.state_clean = not extra and not r.get("failed_modules")
            return chosen | extra
        gone = {sel.struct[fp.old]["module"] for fp in parse_patch(text)
                if fp.old in sel.struct and (fp.new is None or fp.new != fp.old)}
        got = sel.readers(r["changed"], gone)
        log("state", name, r["n"], "items", r["changed"][:3], "->", len(got))
        return chosen | got

    state_clean = False
    n_state = 0
    extra, norec = {}, frozenset()      # norec: fixture files this commit edits (their record numbers may shift)

    def failed_records(self, sel, proxy, result, spec):
        """(fixture file, record indexes) for the proxy's failing subtests, or None when that cannot be told."""
        if self.id[proxy] in set(result.get("whole", ())):
            return None                       # the proxy failed outside its per-record subtests
        recmap = sel.m.get("rec", {}).get(sel.rev.get(proxy)) or {}
        if len(recmap) != 1:
            return None
        (fx, info), = recmap.items()
        if fx in self.norec:
            return None
        ran = (spec or {}).get("files", {}).get(fx)      # records the proxy was run on, when it was sliced
        idxs = set()
        for nodeid, msg in result.get("sub", ()):
            if nodeid != self.id[proxy]:
                continue
            m = re.match(r"(?:\(execute\) )?(\d+), ", msg)   # the tests title a record "<position>, <sql>"
            if not m:
                return None
            pos = int(m.group(1)) - 1
            if ran is not None:
                if pos >= len(ran):
                    return None
                pos = ran[pos]
            if pos >= info["n"]:
                return None
            idxs.add(pos)
        if not idxs and self.id[proxy] in set(result.get("failed", ())):
            return None
        return fx, sorted(idxs)

    def self_slice(self, sel, test):
        """(fixture, record indexes that reach the changed lines, per-record CPU) for a record-looping test, or None."""
        if sel is None or not sel.line_only or not sel.touched:
            return None
        t = sel.rev.get(test)
        recmap = sel.m.get("selfrec", {}).get(t)
        if not recmap or len(recmap) != 1:
            return None
        (fx, info), = recmap.items()
        if fx in self.norec:
            return None
        mask, seen, inner = 0, False, "optfp" in info
        if "outside_sets" not in info:
            info["outside_sets"] = {f: set(v) for f, v in info.get("outside", {}).items()}
        for f, lo, hi in sel.touched:
            static = sel.m["lines"].get(f, {})
            d = info["lines"].get(f, {})
            out = info["outside_sets"].get(f, ())
            for l in range(lo, hi + 1):
                if t in static.get(l, ()):
                    if not d.get(l):
                        return None          # the test runs this line, but not inside any single record: no slicing
                    mask |= d[l]; seen = True
                elif d.get(l):
                    mask |= d[l]; seen = True
                else:
                    continue
                if l in out:
                    inner = False            # this line also runs outside the optimizer step
        if not seen:
            return None
        return fx, [i for i in range(info["n"]) if mask >> i & 1], info["cpu"], (info if inner else None)

    def taste_spec(self, sel, tests, spec):
        """(sample slice, slice for the remaining records) for a first quick look, or (None, None)."""
        first, rest = {}, {}
        for n in tests:
            recmap = sel.m.get("rec", {}).get(sel.rev.get(n)) or {}
            if len(recmap) != 1:
                return None, None
            (fx, info), = recmap.items()
            if fx in self.norec:
                return None, None
            recs = list((spec or {}).get("files", {}).get(fx, range(info["n"])))
            if len(recs) < TASTE_MIN or fx in first:
                return None, None
            step = len(recs) / TASTE_N
            pick = sorted({recs[int(i * step + step / 2)] for i in range(TASTE_N)})
            first[fx] = pick
            rest[fx] = [i for i in recs if i not in set(pick)]
        return ({"files": first}, {"files": rest}) if first else (None, None)

    def slice_for(self, sel, tests):
        """Fixture records these tests need to run to exercise the changed lines. Returns (slice spec or None, fraction)."""
        if not SLICE or sel is None or not sel.line_only or not sel.touched:
            return None, 1.0
        files, num, den = {}, 0, 0
        for n in tests:
            recmap = sel.m.get("rec", {}).get(sel.rev.get(n))
            if not recmap:
                return None, 1.0
            base = sel.m.get("rec_base", {}).get(sel.rev.get(n), {})
            for f, lo, hi in sel.touched:
                bl = self.base_sets.setdefault((n, f), set(base.get(f, ())))
                if any(l in bl for l in range(lo, hi + 1)):
                    return None, 1.0      # the change also runs outside the per-record loop: every record is affected
            for fx, info in recmap.items():
                if fx in self.norec:
                    return None, 1.0
                mask = 0
                for f, lo, hi in sel.touched:
                    d = info["lines"].get(f)
                    if d:
                        for l in range(lo, hi + 1):
                            mask |= d.get(l, 0)
                idxs = {i for i in range(info["n"]) if mask >> i & 1}
                files[fx] = sorted(set(files.get(fx, ())) | idxs)
                num += len(idxs); den += info["n"]
        return {"files": files}, (num / den if den else 1.0)

    def estimate(self, nums):
        """Expected CPU seconds to run these tests for real (measured per test when the map has it)."""
        c, classes = 0.19, set()
        for n in nums:
            if n in self.cpu_own:
                c += self.cpu_own[n]
                classes.add(self.id[n].rsplit("::", 1)[0])
            else:
                c += self.ms[n] / 1000 * (2.0 if self.file[n] in SLOW_FILES else 1.0)
        return c + sum(self.cpu_setup.get(k, 0.0) for k in classes)

    def left(self):
        return self.deadline - time.time()

    def check(self, name, text, chosen, all_count, sel=None):
        chosen = self._check(name, text, chosen, all_count, sel)
        if HEAVYRUN and VERIFY and chosen:
            try:
                chosen = self.heavy_run(name, text, chosen)
            except Exception as e:
                log("heavy-run", name, "error", repr(e))
        return chosen

    def heavy_run(self, name, text, chosen):
        """Expensive tests that are cheap to run for real here (DuckDB answers come from the memo): run them, keep
        the ones that fail. Taken cheapest first, as long as the CPU spent stays well under the seconds saved."""
        heavy = sorted((n for n in chosen if self.ms[n] >= HEAVY_SECS * 1000), key=lambda n: self.cpu_own.get(n, self.ms[n] / 1000))
        if not heavy or self.left() < 25:
            return chosen
        if any(fp.old is None or fp.new is None or fp.old != fp.new for fp in parse_patch(text)):
            return chosen
        patched = self.patched(text)
        if patched is None or any(f.startswith("tests/fixtures/") for f in patched):
            return chosen
        base = cost_ms(chosen, self.ms) / 1000
        pick = []
        for k in range(1, len(heavy) + 1):
            est = self.estimate(heavy[:k])
            gain = base - cost_ms(chosen - set(heavy[:k]), self.ms) / 1000
            if est <= HEAVYRUN_RATIO * gain:
                pick = heavy[:k]
        if not pick:
            return chosen
        est = self.estimate(pick)
        r = self.start().run(patched, [self.id[n] for n in pick], stop=False, limit=min(max(15.0, 5 * est), self.left() - 5))
        self.cpu += r.get("cpu", 0)
        clean = r.get("rc") in (0, 1) and not r.get("collect") and not r.get("crash")
        passed, failed = set(r.get("passed", ())), set(r.get("failed", ()))
        drop = {n for n in pick if clean and self.id[n] in passed and self.id[n] not in failed}
        log("heavy-run", name, [self.id[n].split("::")[-1] for n in pick], "est", round(est, 2), "cpu", r.get("cpu"), "dropped", len(drop))
        return chosen - drop

    def _check(self, name, text, chosen, all_count, sel=None):
        if not VERIFY or not chosen or self.left() < 20:
            return chosen
        wide = len(chosen) > 0.5 * all_count        # nearly everything selected: only the comparison probe is worth its CPU
        if wide and not WIDE_PROBE:
            return chosen
        if any(fp.old is None or fp.new is None or fp.old != fp.new for fp in parse_patch(text)):
            return chosen
        patched = self.patched(text)
        if patched is None:
            return chosen
        if FIXSLICE and not wide and all(f.startswith("tests/fixtures/") and f.endswith(".sql") for f in patched) \
                and any(self.ms[n] >= HEAVY_SECS * 1000 for n in chosen) and self.left() > 30:
            # Only fixture records changed, and an expensive test reads the file. Run every candidate for real with the
            # fixture loaders yielding just the records that differ from the pinned commit: unchanged records behave
            # exactly as before, so a candidate fails here if and only if it fails on the whole file.
            order = sorted(chosen, key=lambda n: self.ms[n])
            r = self.start().run(patched, [self.id[n] for n in order], stop=False, limit=min(90.0, self.left() - 5),
                                 slice={"changed": str(SG / "tests" / "fixtures")})
            self.cpu += r.get("cpu", 0)
            clean = r.get("rc") in (0, 1) and not r.get("collect") and not r.get("crash")
            passed, failed = set(r.get("passed", ())), set(r.get("failed", ()))
            keep = {n for n in chosen if self.id[n] in failed or self.id[n] not in passed} if clean else set(chosen)
            log("fixslice", name, "candidates", len(chosen), "cpu", r.get("cpu"), "kept", len(keep), "clean", clean)
            return keep
        if not all(f.endswith(".py") for f in patched):
            return chosen          # a data file some candidate reads changed: running it would almost surely just confirm that
        heavy = {n for n in chosen if self.ms[n] >= HEAVY_SECS * 1000}
        known_fail = False
        # A patch that only swaps the operator of one comparison: run some of the cheapest candidates and apply the
        # old and the new operator side by side to the values that actually reach that line (and to nearby inputs).
        # If the two never disagree over enough executions, the change is not observable and nothing needs to run.
        if EQUIV and not getattr(sel, "cond_applied", False) and len(patched) == 1 and self.left() > 20:
            (rel, new_src), = patched.items()
            hunk = "\n".join(t for fp in parse_patch(text) for t in fp.added_text() + fp.removed_text())
            sw = compare_swap((SG / rel).read_text(encoding="utf-8"), new_src) if re.search(r"==|!=|<|>|\bis\b|\bin\b", hunk) else None
            if sw:
                sw["file"] = rel
                # cheapest candidates first, at most 8 per test class so the operands seen come from several places
                cost = lambda n: self.cpu_own.get(n, self.ms[n] / 1000)
                pick, used, per_cls = [], 0.19, {}
                for n in sorted(chosen - heavy, key=cost):
                    k = self.id[n].rsplit("::", 1)[0]
                    if per_cls.get(k, 0) >= EQUIV_PER_CLASS:
                        continue
                    c = cost(n) + 0.05                      # plus per-test runner overhead
                    if pick and (used + c > EQUIV_BUDGET or len(pick) >= EQUIV_MAX_TESTS):
                        break
                    pick.append(n); used += c; per_cls[k] = per_cls.get(k, 0) + 1
                if pick:
                    r = self.start().run(patched, [self.id[n] for n in pick], stop=True, limit=min(max(10.0, 6 * used), self.left() - 5), probe=sw)
                    self.cpu += r.get("cpu", 0)
                    pr = r.get("probe") or {}
                    passed = r.get("rc") == 0 and not r.get("failed") and not r.get("collect") and not r.get("crash") \
                        and set(r.get("passed", ())) >= {self.id[n] for n in pick}
                    log("equiv", name, sw["old"], "->", sw["new"], "tests", len(pick), "cpu", r.get("cpu"), "probe", pr, "passed", passed)
                    if not passed:
                        known_fail = True            # a cheap candidate fails; the expensive ones still get their own checks
                    elif pr.get("agree") and pr.get("n", 0) >= EQUIV_MIN_RUNS and pr.get("tests", 0) >= min(EQUIV_MIN_TESTS, len(chosen - heavy)):
                        return set()
                    else:
                        chosen = chosen - set(pick)      # these passed for real; carry on with the rest
        if wide:
            return chosen
        # An expensive test that loops over fixture records, and a change that only some records reach: run the test
        # for real on just those records (cheapest first). Records that never reach the changed lines behave exactly
        # as before, so the test fails on the whole file if and only if it fails on these.
        settled = set()
        if SELF and heavy and self.left() > 25:
            for hv in sorted(heavy, key=lambda n: -self.ms[n]):
                got = self.self_slice(sel, hv)
                if COND and getattr(sel, "cond_applied", False):
                    # a one-condition edit: the recorded values say, query by query, where the old and the new
                    # condition could disagree. Only those records can behave differently.
                    try:
                        import cond
                        fp0 = parse_patch(text)[0]
                        old0 = (SG / fp0.old).read_text(encoding="utf-8")
                        crec = cond.touched_records(sel.rev.get(hv), fp0.old, old0, fp0.apply(old0), parse_src,
                                                    set(fp0.removed) | set(fp0.insert_points))
                    except Exception:
                        crec = None
                    info0 = (sel.m.get("selfrec", {}).get(sel.rev.get(hv)) or {}).get(crec[0]) if crec else None
                    if crec and crec[1] and info0 and crec[0] not in self.norec:
                        if got:
                            got = (got[0], [i for i in got[1] if i in set(crec[1])] or list(crec[1]), got[2], got[3])
                        else:
                            got = (crec[0], list(crec[1]), info0["cpu"], None)
                        log("cond-records", name, len(crec[1]))
                if not got:
                    continue
                fx, idxs, costs, inner = got
                gain = (cost_ms(chosen, self.ms) - cost_ms(chosen - {hv}, self.ms)) / 1000
                changed_known = False
                if OPT and inner is not None:
                    # Every changed line runs only inside the optimizer step of this test. So first redo just that
                    # step for the records that reach the change and compare each optimized tree with the one from
                    # the pinned commit. A record whose tree is identical goes on exactly as before.
                    est_o = 0.3 + sum(inner["optcpu"][i] for i in idxs)
                    if est_o <= OPT_RATIO * gain:
                        todo, first, hopeless = list(idxs), {}, False
                        setup = 0.19 + self.cpu_setup.get(self.id[hv].rsplit("::", 1)[0], 0.0)
                        if len(idxs) >= 30:
                            # look at ten evenly spaced records first: if most of them changed, running all the
                            # changed ones for real is out of reach and the rest of this step is not worth doing
                            step = len(idxs) / 10
                            sample = sorted({idxs[int(k * step + step / 2)] for k in range(10)})
                            o1 = self.start().opt(patched, fx, inner["schema"], sample, limit=min(15.0, self.left() - 5))
                            self.cpu += (o1 or {}).get("cpu", 0)
                            if o1 and o1.get("ok"):
                                first = o1["fps"]
                                frac = sum(1 for i in sample if first.get(str(i)) != inner["optfp"][i]) / len(sample)
                                todo = [i for i in idxs if i not in set(sample)]
                                if setup + frac * sum(costs[i] for i in idxs) > 1.5 * SELF_RATIO * gain:
                                    log("opt-step", name, "sample changed %.0f%%" % (100 * frac), "cpu", o1.get("cpu"), "-> keep")
                                    settled.add(hv)
                                    hopeless = True
                        if hopeless:
                            continue
                        o = self.start().opt(patched, fx, inner["schema"], todo, limit=min(max(15.0, 6 * est_o), self.left() - 5))
                        self.cpu += (o or {}).get("cpu", 0)
                        if o and o.get("ok"):
                            o["fps"].update(first)
                            diff = [i for i in idxs if o["fps"].get(str(i)) != inner["optfp"][i]]
                            log("opt-step", name, "records", len(idxs), "changed", len(diff), "cpu", o.get("cpu"))
                            if not diff:
                                chosen = chosen - {hv}
                                settled.add(hv)
                                continue
                            idxs, changed_known = diff, True
                est = 0.19 + self.cpu_setup.get(self.id[hv].rsplit("::", 1)[0], 0.0) + sum(costs[i] for i in idxs)
                if est > SELF_RATIO * gain:
                    log("self-slice", name, "records", len(idxs), "skipped: est", round(est, 1), "gain", round(gain, 1))
                    if changed_known:
                        settled.add(hv)      # the optimized queries did change and running them all costs too much: keep
                    continue
                # one run, cheapest records first, each record checked right after it is computed: a failing test
                # stops at its first failing record
                order = sorted(idxs, key=lambda i: (costs[i] < 0.03, costs[i]))
                r = self.start().run(patched, [self.id[hv]], stop=True, limit=min(max(15.0, 5 * est), self.left() - 5),
                                     slice={"ordered": {fx: order}}, lazy=True)
                self.cpu += r.get("cpu", 0); used = r.get("cpu", 0) or 0
                ok = r.get("rc") == 0 and not r.get("failed") and not r.get("collect") and not r.get("crash") \
                    and self.id[hv] in set(r.get("passed", ()))
                log("self-slice", name, self.id[hv].split("::")[-1], "records", len(idxs), "cpu", round(used, 2), "dropped" if ok else "kept")
                settled.add(hv)
                if ok:
                    chosen = chosen - {hv}
            heavy = heavy & chosen
        # An expensive test with a cheaper "proxy" (another class's test that reads the same fixture and executes
        # nearly the same lines): if the proxy also reaches this change and passes for real, drop the expensive one.
        if PROXY and heavy - settled:
            pairs = {}
            for hv in heavy - settled:
                for sim, p in self.proxy.get(hv, ()):
                    if sim >= PROXY_SIM and p in chosen and p not in heavy and self.ms[p] < self.ms[hv]:
                        pairs[hv] = p
                        break
            if pairs:
                px = sorted(set(pairs.values()), key=lambda n: self.ms[n])
                spec, frac = self.slice_for(sel, px)
                est = 0.25 + (self.estimate(px) - 0.19) * frac
                gain = (cost_ms(chosen, self.ms) - cost_ms(chosen - set(pairs), self.ms)) / 1000
                if est <= 0.6 * gain and self.left() > 20:
                    # Taste first: run the proxy on a few evenly spaced records. If several already fail, the change
                    # is broad, the expensive test stays, and the rest of the proxy run is not worth its CPU.
                    taste, rest = self.taste_spec(sel, px, spec) if TASTE else (None, None)
                    t = None
                    if taste:
                        t = self.start().run(patched, [self.id[n] for n in px], stop=False, limit=min(15.0, self.left() - 5), slice=taste)
                        self.cpu += t.get("cpu", 0)
                        tclean = t.get("rc") in (0, 1) and not t.get("collect") and not t.get("crash")
                        nfail = len(t.get("sub", ())) + len(t.get("whole", ()))
                        if not tclean or nfail >= TASTE_STOP or (t.get("failed") and not t.get("sub")):
                            log("proxy-taste", name, "failures", nfail, "cpu", t.get("cpu"), "-> keep")
                            return chosen
                        spec = rest
                    r = self.start().run(patched, [self.id[n] for n in px], stop=not REFINE, limit=min(max(15.0, 6 * est), self.left() - 5), slice=spec, max_sub=REFINE_MAX if REFINE else 0)
                    self.cpu += r.get("cpu", 0)
                    log("proxy-slice", name, "records %.0f%%" % (100 * frac), "taste cpu", t.get("cpu") if t else None)
                    clean = r.get("rc") in (0, 1) and not r.get("collect") and not r.get("crash")
                    tfailed = set(t.get("failed", ())) if t else set()
                    passed = {n for n in px if clean and self.id[n] in set(r.get("passed", ())) and self.id[n] not in set(r.get("failed", ()))
                              and self.id[n] not in tfailed}
                    drop = {hv for hv, p in pairs.items() if p in passed}
                    if drop:
                        # guard: if any other candidate can no longer even be imported, the breakage is broad -> keep all
                        others = sorted(chosen - heavy - set(px), key=lambda n: self.ms[n])
                        if others:
                            g = self.v.run(patched, [self.id[n] for n in others], stop=True, limit=min(30.0, self.left() - 5), collect_only=True)
                            self.cpu += g.get("cpu", 0)
                            if g.get("rc") != 0 or g.get("collect") or g.get("crash") or g.get("failed"):
                                log("proxy", name, "guard: candidates fail to import -> keep all")
                                return chosen
                    log("proxy", name, [self.id[n].split("::")[-1] for n in px], "cpu", r.get("cpu"), "dropped", len(drop))
                    chosen = chosen - drop - passed
                    heavy = heavy - drop
                    if len(passed) < len(px):
                        # A proxy failed. Its failing subtests name the fixture records whose result changed; run the
                        # expensive test for real on just those records. Records the proxy still passes behave as before.
                        if REFINE and clean and self.left() > 30:
                            for hv, p in pairs.items():
                                if p in passed or hv not in chosen:
                                    continue
                                recs = None if r.get("early") else self.failed_records(sel, p, r, spec)
                                if recs and t:
                                    more = self.failed_records(sel, p, t, taste)
                                    recs = (recs[0], sorted(set(recs[1]) | set(more[1]))) if more else None
                                if not recs or not recs[1]:
                                    continue
                                fx, idxs = recs
                                est2 = 1.5 + len(idxs) * 0.45
                                gain2 = (cost_ms(chosen, self.ms) - cost_ms(chosen - {hv}, self.ms)) / 1000
                                if est2 > REFINE_RATIO * gain2:
                                    log("refine", name, "records", len(idxs), "too many: est", round(est2, 1), "gain", round(gain2, 1))
                                    continue
                                others = sorted(chosen - heavy - set(px), key=lambda n: self.ms[n])
                                if others:
                                    g = self.v.run(patched, [self.id[n] for n in others], stop=True, limit=min(30.0, self.left() - 5), collect_only=True)
                                    self.cpu += g.get("cpu", 0)
                                    if g.get("rc") != 0 or g.get("collect") or g.get("crash") or g.get("failed"):
                                        log("refine", name, "guard: candidates fail to import -> keep all")
                                        return chosen
                                h = self.v.run(patched, [self.id[hv]], stop=True, limit=min(max(20.0, 4 * est2), self.left() - 5),
                                               slice={"files": {fx: idxs}}, lazy=True)
                                self.cpu += h.get("cpu", 0)
                                ok = h.get("rc") == 0 and not h.get("failed") and not h.get("collect") and not h.get("crash") \
                                    and self.id[hv] in set(h.get("passed", ()))
                                log("refine", name, self.id[hv].split("::")[-1], "records", len(idxs), "cpu", h.get("cpu"), "dropped" if ok else "kept")
                                if ok:
                                    chosen = chosen - {hv}
                        return chosen                 # a proxy failed: keep everything else as selected
        rest = sorted(chosen - heavy, key=lambda n: self.ms[n])
        if not rest or known_fail:
            return chosen
        est = self.estimate(rest)
        gain = cost_ms(chosen, self.ms) / 1000 if (SKIP_HEAVY or not heavy) else (cost_ms(chosen, self.ms) - cost_ms(heavy, self.ms)) / 1000
        ratio = VERIFY_RATIO_HEAVY if (SKIP_HEAVY and heavy) else VERIFY_RATIO
        if est > ratio * gain:
            log("verify", name, "skipped: est", round(est, 2), "gain", round(gain, 2))
            return chosen
        r = self.start().run(patched, [self.id[n] for n in rest], stop=True, limit=min(max(10.0, 6 * est), self.left() - 5))
        self.cpu += r.get("cpu", 0)
        ok = r.get("rc") == 0 and not r.get("failed") and not r.get("collect") and not r.get("crash") \
            and set(r.get("passed", ())) >= {self.id[n] for n in rest}
        log("verify", name, "tests", len(rest), "est", round(est, 2), "cpu", r.get("cpu"), "all-pass" if ok else "kept")
        if not ok:
            return chosen
        return set() if SKIP_HEAVY else heavy


_TREES = {}


def parse_src(src):
    """ast.parse with a small memo: the same file text is parsed several times per commit. Shared trees: read-only."""
    key = (len(src), hash(src))
    t = _TREES.get(key)
    if t is None:
        if len(_TREES) > 12:
            _TREES.clear()
        t = _TREES[key] = ast.parse(src)
    return t


def _code_same(a, b):
    """Two compiled functions/classes that execute the same instructions on the same constants and names.
    Line numbers and the names of plain local variables are ignored: neither can change what the code does."""
    if a.co_code != b.co_code or a.co_exceptiontable != b.co_exceptiontable:
        return False
    if (a.co_argcount, a.co_posonlyargcount, a.co_kwonlyargcount, a.co_flags, a.co_names, a.co_freevars, a.co_cellvars,
            a.co_name, a.co_qualname, len(a.co_varnames), len(a.co_consts)) != \
       (b.co_argcount, b.co_posonlyargcount, b.co_kwonlyargcount, b.co_flags, b.co_names, b.co_freevars, b.co_cellvars,
            b.co_name, b.co_qualname, len(b.co_varnames), len(b.co_consts)):
        return False
    nargs = a.co_argcount + a.co_kwonlyargcount + bool(a.co_flags & 0x04) + bool(a.co_flags & 0x08)
    if a.co_varnames[:nargs] != b.co_varnames[:nargs]:
        return False                              # parameter names are part of the call interface
    if a.co_varnames != b.co_varnames and {"locals", "vars", "eval", "exec", "dir"} & set(a.co_names):
        return False                              # code that can look at its own local names
    for x, y in zip(a.co_consts, b.co_consts):
        if hasattr(x, "co_code") or hasattr(y, "co_code"):
            if not (hasattr(x, "co_code") and hasattr(y, "co_code") and _code_same(x, y)):
                return False
        elif type(x) is not type(y) or repr(x) != repr(y):
            return False
    return True


def _stmts_same(xs, ys, name):
    if len(xs) != len(ys):
        return False
    for x, y in zip(xs, ys):
        if ast.dump(x) == ast.dump(y):
            continue
        if isinstance(x, ast.ClassDef) and isinstance(y, ast.ClassDef) and x.name == y.name and \
                ast.dump(ast.ClassDef(x.name, x.bases, x.keywords, [], x.decorator_list, getattr(x, "type_params", []))) == \
                ast.dump(ast.ClassDef(y.name, y.bases, y.keywords, [], y.decorator_list, getattr(y, "type_params", []))):
            if not _stmts_same(x.body, y.body, name):
                return False
            continue
        if not (isinstance(x, (ast.FunctionDef, ast.AsyncFunctionDef)) and type(x) is type(y)):
            return False                          # a differing class-level or module-level statement: not our case
        try:
            ca = compile(ast.Module([x], []), name, "exec", dont_inherit=True)
            cb = compile(ast.Module([y], []), name, "exec", dont_inherit=True)
        except Exception:
            return False
        if not _code_same(ca, cb):
            return False
    return True


class _DropNoOps(ast.NodeTransformer):
    """Remove statements that cannot do anything: `pass`, a bare constant, and inside a function an assignment of a
    constant to a plain local name that the function never reads."""

    def _body(self, stmts, dead=()):
        out = []
        for i, st in enumerate(stmts):
            if isinstance(st, ast.Pass):
                continue
            if isinstance(st, ast.Expr) and isinstance(st.value, ast.Constant) and not (i == 0 and isinstance(st.value.value, str)):
                continue
            if isinstance(st, ast.Assign) and len(st.targets) == 1 and isinstance(st.targets[0], ast.Name) \
                    and isinstance(st.value, ast.Constant) and st.targets[0].id in dead:
                continue
            out.append(st)
        return out or [ast.Pass()]

    def generic_visit(self, node):
        super().generic_visit(node)
        dead = ()
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            read, blocked = set(), False
            for n in ast.walk(node):
                if isinstance(n, ast.Name) and not isinstance(n.ctx, ast.Store):
                    read.add(n.id)
                elif isinstance(n, (ast.Global, ast.Nonlocal)):
                    read.update(n.names)
                elif isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Name):
                    read.add(n.target.id)        # x += 1 reads x
                elif isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id in ("locals", "vars", "eval", "exec", "dir"):
                    blocked = True
            if not blocked:
                stored = {n.id for n in ast.walk(node) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store)}
                dead = stored - read
        for field in ("body", "orelse", "finalbody"):
            v = getattr(node, field, None)
            if isinstance(v, list) and v and isinstance(v[0], ast.stmt):
                setattr(node, field, self._body(v, dead) if field == "body" or v else v)
        return node


def _outer_functions(tree):
    """{qualified name: node} for functions at module level and methods of (nested) classes."""
    out = {}
    def rec(body, prefix):
        for st in body:
            if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef)):
                key = prefix + st.name
                out[key] = None if key in out else st       # a name defined twice: ambiguous, never matched
            elif isinstance(st, ast.ClassDef):
                rec(st.body, prefix + st.name + ".")
    rec(tree.body, "")
    return out


def same_program_at(fp, old_tree, new_tree, name):
    """Like same_program, but only looks at the functions the patch touches (cheap on very large files).
    False unless every changed line, on both sides, sits inside a function that exists in both versions."""
    try:
        old_lines = set(fp.removed) | set(fp.insert_points)
        new_lines, delta = set(), 0
        for start, body in fp.hunks:
            n = start + delta
            for tag, _ in body:
                if tag == "+":
                    new_lines.add(n); n += 1; delta += 1
                elif tag == "-":
                    new_lines.add(n); delta -= 1          # the line now at the place of a removal
                else:
                    n += 1
        fo, fn = _outer_functions(old_tree), _outer_functions(new_tree)
        if set(fo) != set(fn):
            return False
        touched = set()
        for lines, funcs in ((old_lines, fo), (new_lines, fn)):
            spans = [(v.lineno, v.end_lineno, k) for k, v in funcs.items() if v is not None]
            for ln in lines:
                hit = [k for a, b, k in spans if a <= ln <= b]
                if len(hit) != 1:
                    return False
                touched.add(hit[0])
        for k in touched:
            x, y = fo[k], fn[k]
            if x is None or y is None:
                return False
            a, b = _DropNoOps().visit(ast.Module([copy.deepcopy(x)], [])), _DropNoOps().visit(ast.Module([copy.deepcopy(y)], []))
            if ast.dump(a) != ast.dump(b) and not _stmts_same(a.body, b.body, name):
                return False
        return bool(touched)
    except Exception:
        return False


def same_program(old_tree, new_tree, name):
    """True when the edit cannot change what the file does: after removing statements that do nothing, the two
    versions are the same tree, or every function that still differs compiles to the same instructions (for example
    a renamed local variable, or code after a return)."""
    try:
        a, b = _DropNoOps().visit(old_tree), _DropNoOps().visit(new_tree)
        if ast.dump(a) == ast.dump(b):
            return True
        return _stmts_same(a.body, b.body, name)
    except Exception:
        return False


def cond_trim(name, text, sel, chosen, pending):
    """One-condition edits (a swapped comparison or and/or, an added or removed `not`) in run-time code: keep only
    the tests in which the old and the new condition could ever give a different answer, according to the values
    each test was seen to produce there at the pinned commit. A test where they always agree runs exactly as before."""
    sel.cond_applied = False
    if not COND or pending or not chosen:
        return chosen
    fps = parse_patch(text)
    if len(fps) != 1:
        return chosen
    fp = fps[0]
    if fp.binary or fp.old is None or fp.new is None or fp.old != fp.new or not fp.old.endswith(".py"):
        return chosen
    import cond
    old = (SG / fp.old).read_text(encoding="utf-8")
    r = cond.touched(fp.old, old, fp.apply(old), parse_src, set(fp.removed) | set(fp.insert_points))
    if r is None:
        return chosen
    hit, ran, what = r
    keep = set()
    for n in chosen:
        i = sel.rev.get(n)
        if i is None or not (ran >> i & 1) or (hit >> i & 1):
            keep.add(n)                      # may differ, or the recorder has nothing on this test
    log("cond", name, what, len(chosen), "->", len(keep))
    sel.cond_applied = True
    return keep


def telemetry_code(lines, in_final, wide):
    """DIAGNOSTIC ONLY. One digit saying what happened to the big TPC-DS test on a commit that pointed at it:
    1 dropped by an exact rule, 2 dropped because the stand-in test passed, 3 kept: its own records failed for real,
    4 kept: the optimizer's output changed for too many queries, 5 kept: the stand-in test failed on a sample,
    6 kept: the stand-in test failed in full, 7 kept: nearly every test was selected so nothing was checked,
    8 kept: no check could run."""
    has = lambda *words: any(all(w in l for w in words) for l in lines)
    if not in_final:
        return 2 if (any(l.startswith("proxy ") and not l.rstrip().endswith("dropped 0") for l in lines)
                     or has("refine", "dropped")) else 1
    if any(l.startswith("self-slice") and l.rstrip().endswith("kept") for l in lines) or has("fixslice"):
        return 3
    if has("opt-step", "-> keep") or (has("opt-step", "changed") and has("self-slice", "skipped")):
        return 4
    if has("proxy-taste"):
        return 5
    if any(l.startswith("proxy ") for l in lines) or has("refine"):
        return 6
    return 7 if wide else 8


def telemetry_wide(text, lines):
    """DIAGNOSTIC ONLY. Four digits describing a commit on which more than half of all tests were selected:
    file (1 tokens.py, 2 parser.py, 3 generator.py, 4 dialects/dialect.py, 5 expressions/, 6 other sqlglot, 7 not
    sqlglot source, 8 several files), how it was handled (1 import check found changed values, 2 some module no
    longer imports, 3 too many changed values, 4 import check found nothing, 5 no import check), type of the single
    changed literal (1 true/false, 2 text, 3 number, 4 None, 5 not a single literal), and how many values the import
    check reported as changed (9 = nine or more)."""
    fps = parse_patch(text)
    f = (fps[0].old or fps[0].new or "") if len(fps) == 1 else None
    if f is None:
        d1 = 8
    elif not (f.startswith("sqlglot/") and f.endswith(".py")):
        d1 = 7
    else:
        d1 = {"sqlglot/tokens.py": 1, "sqlglot/parser.py": 2, "sqlglot/generator.py": 3, "sqlglot/dialects/dialect.py": 4}.get(
            f, 5 if f.startswith("sqlglot/expressions/") else 6)
    st = [l for l in lines if l.startswith("state ")]
    d2, d4 = 5, 0
    for l in st:
        m = re.search(r" (\d+) items ", l)
        if m:
            d2, d4 = 1, min(9, int(m.group(1)))
        elif "fail to import" in l or "import failed" in l:
            d2 = 2
        elif "many items" in l:
            d2 = 3
        elif "no change" in l:
            d2 = 4
    d3 = 5
    try:
        if f and d1 < 7:
            import cond
            old = (SG / f).read_text(encoding="utf-8")
            pair = cond._diff(parse_src(old), parse_src(fps[0].apply(old)), set(fps[0].removed) | set(fps[0].insert_points))
            if pair and isinstance(pair[0], ast.Constant) and isinstance(pair[1], ast.Constant):
                v = pair[0].value
                d3 = 1 if isinstance(v, bool) else 2 if isinstance(v, (str, bytes)) else 3 if isinstance(v, (int, float)) else 4
    except Exception:
        pass
    return d1 * 1000 + d2 * 100 + d3 * 10 + d4


def telemetry(results, codes, n_state, ms):
    """DIAGNOSTIC ONLY. Adds extra, unneeded tests to the busiest worker of some commits so that the total
    simulated time grows by exactly  n_state * 10 s + 0.dddd s, where the d are the per-commit codes above
    (largest first). Reading the practice score then shows which path our own program took. It never removes
    a test, so it cannot cause a miss. Not for a final entry."""
    digits = sorted(codes, reverse=True)[:4]
    if len(codes) > 4:
        digits[0] = 9
    digits += [0] * (4 - len(digits))
    target = n_state * 10000 + digits[0] * 1000 + digits[1] * 100 + digits[2] * 10 + digits[3]
    if TELEM2:                                     # second diagnostic: (number of wide commits) * 10 s + 4 digits about the first
        target = n_state
    log("telemetry", "state calls", n_state, "codes", codes, "extra ms", target)
    for name, workers in results:
        if target <= 0:
            break
        if not workers:
            continue
        used = {n for w in workers for n in w}
        pool = sorted((n for n in ms if n not in used and ms[n] > 0), key=lambda n: -ms[n])
        room = min(target, 60000)
        pick, left = [], room
        for n in pool:
            if ms[n] <= left:
                pick.append(n); left -= ms[n]
        if left:                                   # could not hit the amount exactly on this commit: try the next
            continue
        loads = [sum(ms[n] for n in w) for w in workers]
        workers[loads.index(max(loads))].extend(pick)
        target -= room
    if target > 0:
        log("telemetry", "could not place", target)


_FLAGS = None


def flag_select(name, text, sel):
    """An edit that only flips one class-level `NAME = True/False`: the tests that can notice are the ones that
    actually looked at that value when the unmodified code ran (recorded at the pinned commit; merely copying the
    value around does not count). Returns that set, or None when this rule does not apply - including when the value
    is looked at while sqlglot itself loads, where the import check has to decide."""
    global _FLAGS
    if not FLAGS:
        return None
    fps = parse_patch(text)
    if len(fps) != 1:
        return None
    fp = fps[0]
    if fp.binary or fp.old is None or fp.new is None or fp.old != fp.new or not (fp.old.startswith("sqlglot/") and fp.old.endswith(".py")):
        return None
    if _FLAGS is None:
        try:
            _FLAGS = pickle.loads(zlib.decompress((Path(__file__).resolve().parent / "flags.pkl.z").read_bytes()))
        except Exception:
            _FLAGS = {}
    if not _FLAGS:
        return None
    import cond
    old = (SG / fp.old).read_text(encoding="utf-8")
    try:
        a, b = parse_src(old), parse_src(fp.apply(old))
    except SyntaxError:
        return None
    pair = cond._diff(a, b, set(fp.removed) | set(fp.insert_points))
    if pair is None:
        return None
    x, y = pair
    if not (isinstance(x, ast.Constant) and isinstance(y, ast.Constant) and isinstance(x.value, bool)
            and isinstance(y.value, bool) and x.value != y.value):
        return None

    def find(body, path):                         # the class-level statement whose whole value is this constant
        for st in body:
            if isinstance(st, ast.ClassDef):
                r = find(st.body, path + [st.name])
                if r:
                    return r
            elif isinstance(st, (ast.Assign, ast.AnnAssign)) and st.value is x and path:
                tgt = st.targets[0] if isinstance(st, ast.Assign) and len(st.targets) == 1 else getattr(st, "target", None)
                if isinstance(tgt, ast.Name):
                    return (fp.old, ".".join(path), tgt.id, st.lineno)
        return None

    key = find(a.body, [])
    site = _FLAGS["sites"].get(key) if key else None
    if site is None or site[1]:
        return None
    mask = site[0] | _FLAGS["always"]
    out = {n for n in sel.all if (lambda i: i is None or (mask >> i & 1))(sel.rev.get(n))}
    log("flag", name, key[1] + "." + key[2], "->", len(out))
    return out


def by_file(name, text, sel, chk):
    """A commit that edits several files: select and check each file's edit on its own, with the rest of the commit
    applied whenever something is run for real, and take the union. Returns (static count, chosen) or None when the
    commit is not a plain multi-file edit (then the caller handles it as one piece)."""
    parts = [p for p in re.split(r"(?m)^(?=diff --git )", text) if p.strip()]
    if len(parts) < 2:
        return None
    fps = parse_patch(text)
    if len(fps) != len(parts) or any(fp.binary or fp.old is None or fp.new is None or fp.old != fp.new for fp in fps):
        return None
    whole = chk.patched(text)
    if whole is None:
        return None
    full, fpend = sel.select(text)
    full = set(full).union(*[p for _, p in fpend])
    static = set()
    for part in parts:
        ch, pend = sel.select(part)
        static |= set(ch).union(*[p for _, p in pend])
    if static != full:
        log("multi", name, "parts do not add up", len(static), len(full))
        return None
    if len(full) > 0.5 * len(sel.all) and not WIDE_PROBE:
        return None
    total = set()
    for part in parts:
        mine = chk.patched(part)
        if mine is None:
            return None
        chk.extra = {f: v for f, v in whole.items() if f not in mine}
        chk.norec = frozenset(f[len("tests/fixtures/"):] for f in whole if f.startswith("tests/fixtures/"))
        ch, pend = sel.select(part)
        flagged = flag_select(name, part, sel)
        if flagged is not None:
            ch, pend = flagged, []
            sel.pending, sel.line_only = [], False
        ch = cond_trim(name, part, sel, ch, pend)
        if pend:
            ch = chk.resolve(name, part, sel, ch, pend)
            if chk.state_clean:              # importing the edited code changed nothing: only run-time use matters
                ch = cond_trim(name, part, sel, ch, [])
        if ch:
            ch = chk.check(name, part, ch, len(sel.all), sel)
        total |= set(ch)
    log("multi", name, "files", len(parts), "static", len(full), "->", len(total))
    return len(full), total


def main():
    tests = json.loads((DATA / "tests.json").read_text())["tests"]
    ms = {t["number"]: int(t["seconds"] * 1000 + 0.5) for t in tests}
    with open(MAP, "rb") as fh:
        raw = fh.read()
    sel = Selector(pickle.loads(zlib.decompress(raw) if MAP.endswith(".z") else raw), tests)
    chk = Checker(tests, ms)
    chk.proxy = {sel.tr[t]: [(sim, sel.tr[o]) for sim, o in v if sel.tr[o] is not None]
                 for t, v in sel.m.get("proxy", {}).items() if sel.tr[t] is not None}
    chk.cpu_own = {sel.tr[t]: c for t, c in sel.m.get("cpu_own", {}).items() if sel.tr[t] is not None}
    chk.cpu_setup = sel.m.get("cpu_setup", {})
    try:                                      # real CPU of tests whose DuckDB queries are answered from the memo
        here = Path(__file__).resolve().parent
        memo_cost = json.loads((here / "duck_cost.json").read_text()) if (here / "duck.pkl.z").exists() else {}
    except Exception:
        memo_cost = {}
    num = {v: k for k, v in chk.id.items()}
    for nid, c in memo_cost.items():
        if nid in num:
            chk.cpu_own[num[nid]] = c
    patches = sorted((DATA / "commits").glob("*.patch"))
    if os.environ.get("BR_ONLY"):               # development aid: restrict to listed commit ids
        only = set(open(os.environ["BR_ONLY"]).read().split())
        patches = [p for p in patches if p.stem in only]
    # the batch limit is 3 minutes (4.5 in the larger final); stop running things for real well before it
    chk.deadline = T0 + float(os.environ.get("BR_BUDGET", "110" if len(patches) <= 45 else "170"))
    results, codes, wides = [], [], []
    big = [n for n in sel.all if chk.id[n].endswith("::test_execute_tpcds")]
    for patch in patches:
        mark = len(LOGBUF)
        text = patch.read_text(encoding="utf-8", errors="replace")
        try:                                       # every test the plain line/state rules point at, before any narrowing
            c0, p0 = sel.select(text)
            candidates = set(c0).union(*[p for _, p in p0])
        except Exception:
            candidates = set()
        multi = None
        if MULTI:
            try:
                multi = by_file(patch.stem, text, sel, chk)
            except Exception as e:
                log("multi-error", patch.stem, repr(e))
            finally:
                chk.extra, chk.norec = {}, frozenset()
        if multi is not None:
            static_n, chosen = multi
        else:
            try:
                chosen, pending = sel.select(text)
                flagged = None
                try:
                    flagged = flag_select(patch.stem, text, sel)
                except Exception as e:
                    log("flag-error", patch.stem, repr(e))
                if flagged is not None:
                    chosen, pending = flagged, []
                    sel.pending, sel.line_only = [], False
                try:
                    chosen = cond_trim(patch.stem, text, sel, chosen, pending)
                except Exception as e:
                    log("cond-error", patch.stem, repr(e))
                if pending:
                    chosen = chk.resolve(patch.stem, text, sel, chosen, pending)
                    if chk.state_clean:
                        try:
                            chosen = cond_trim(patch.stem, text, sel, chosen, [])
                        except Exception as e:
                            log("cond-error", patch.stem, repr(e))
            except Exception as e:                 # never crash, never guess low
                log("fallback", patch.stem, repr(e)); chosen = set(sel.all)
            static_n = len(chosen)
            try:
                chosen = chk.check(patch.stem, text, chosen, len(sel.all), sel)
            except Exception as e:
                log("verify-error", patch.stem, repr(e))
        if DROP_HEAVY:
            # DIAGNOSTIC ONLY: never select tests of 3 s or more. Used on the practice board to learn how many
            # commits truly need one (reported as misses) and how much they cost. Not for a final entry.
            only = [x for x in os.environ.get("BR_DROP_ONLY", "").split(",") if x]
            chosen = {n for n in chosen if ms[n] < HEAVY_SECS * 1000
                      or (only and chk.id[n].rsplit("::", 1)[-1] not in only)}
        if TELEM and TELEM2:
            if len(chosen) > 0.5 * len(sel.all):
                wides.append(telemetry_wide(text, LOGBUF[mark:]))
            results.append((patch.stem, pack(chosen, ms, candidates)))
        elif TELEM:
            if big and big[0] in candidates:
                codes.append(telemetry_code(LOGBUF[mark:], big[0] in chosen, len(candidates) > 0.5 * len(sel.all)))
            results.append((patch.stem, pack(chosen, ms, candidates)))
        else:
            print(json.dumps({"commit": patch.stem, "workers": pack(chosen, ms, candidates)}), flush=True)
        log(patch.stem, static_n, len(chosen))
    if TELEM:
        telemetry(results, codes, (len(wides) * 10000 + (wides[0] if wides else 0)) if TELEM2 else chk.n_state, ms)
        for name, workers in results:
            print(json.dumps({"commit": name, "workers": workers}), flush=True)
    if chk.v is not None:
        chk.v.close()
    log("verify cpu", round(chk.cpu, 2))


if __name__ == "__main__":
    main()
