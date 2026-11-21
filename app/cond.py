"""Which tests can possibly behave differently after a one-condition edit, from values recorded at the pinned commit.

cond.pkl.z holds, for every comparison / and-or / not inside a function of sqlglot, what each test observed there
when the unmodified code ran (see the build notes). If an edit only swaps the operator of one such condition, or
adds/removes a `not`, then a test in which the old and the new condition give the same answer every single time
runs exactly as before and cannot change its outcome. This module computes the set of tests for which that is NOT
guaranteed ("touched"), using only those recorded observations and the two versions of the source file.
"""
import ast
import pickle
import zlib
from pathlib import Path

_DATA = None
OPS = (ast.boolop, ast.cmpop, ast.unaryop, ast.operator)


def data():
    global _DATA
    if _DATA is None:
        try:
            _DATA = pickle.loads(zlib.decompress(Path(__file__).with_name("cond.pkl.z").read_bytes()))
        except Exception:
            _DATA = {}
    return _DATA


def _clean(node, lines):
    """True when the patch changes no line of this node (old file line numbers), so it cannot differ."""
    if lines is None:
        return False
    a = getattr(node, "lineno", None)
    if a is None:
        return False
    b = getattr(node, "end_lineno", a) or a
    if b - a > 400:
        return not any(a <= l <= b for l in lines)
    return not any(l in lines for l in range(a, b + 1))


def _diff(x, y, lines=None):
    """Smallest pair of nodes (old, new) containing the only difference, or None if identical / more than one place.
    `lines` (old line numbers the patch touches) lets whole untouched subtrees be skipped without comparing them."""
    if type(x) is not type(y):
        return x, y
    if lines is None or not (hasattr(x, "lineno") or isinstance(x, ast.Module)):
        if ast.dump(x) == ast.dump(y):
            return None
    found = []
    for (_, va), (_, vb) in zip(ast.iter_fields(x), ast.iter_fields(y)):
        if isinstance(va, ast.AST) and isinstance(vb, ast.AST):
            pairs = [(va, vb)]
        elif isinstance(va, list) and isinstance(vb, list):
            if len(va) != len(vb):
                return x, y
            pairs = []
            for p, q in zip(va, vb):
                if isinstance(p, ast.AST) and isinstance(q, ast.AST):
                    pairs.append((p, q))
                elif p != q:
                    return x, y
        elif va != vb:
            return x, y
        else:
            continue
        for p, q in pairs:
            if _clean(p, lines):
                continue
            if isinstance(p, OPS) or isinstance(q, OPS):
                if type(p) is not type(q):
                    return x, y                 # the operator itself changed: the difference is this node
                continue
            r = _diff(p, q, lines)
            if r is not None:
                found.append(r)
                if len(found) > 1:
                    return x, y
    if not found:
        return None
    return found[0]


def _parents(tree):
    par = {}
    for n in ast.walk(tree):
        for c in ast.iter_child_nodes(n):
            par[c] = n
    return par


def _bool_context(node, par):
    """True when only the truthiness of this expression is used."""
    p = par.get(node)
    if isinstance(p, (ast.If, ast.While, ast.IfExp, ast.Assert)) and p.test is node:
        return True
    if isinstance(p, ast.comprehension) and node in p.ifs:
        return True
    if isinstance(p, ast.UnaryOp) and isinstance(p.op, ast.Not):
        return True
    if isinstance(p, ast.BoolOp):
        return _bool_context(p, par)
    return False


def _cmp_value(op, fam, c):
    """Result of comparison operator `op` for one recorded observation; None when it cannot be told."""
    if fam == 0:
        ident, e = c // 3, c % 3
        if op is ast.Is:
            return ident
        if op is ast.IsNot:
            return 1 - ident
        if e == 2:
            return None
        if op is ast.Eq:
            return e
        if op is ast.NotEq:
            return 1 - e
        return None
    lt, e, gt = c // 9, (c // 3) % 3, c % 3
    if op is ast.Lt:
        return None if lt == 2 else lt
    if op is ast.Gt:
        return None if gt == 2 else gt
    if op is ast.Eq:
        return None if e == 2 else e
    if op is ast.NotEq:
        return None if e == 2 else 1 - e
    if op in (ast.LtE, ast.GtE):
        a = lt if op is ast.LtE else gt
        if a == 1 or e == 1:
            return 1
        return None if 2 in (a, e) else 0
    return None


def _bool_eval(is_and, states):
    last = None
    for i, s in enumerate(states):
        if s > 1:
            return None, i
        last = (s, i)
        if (s == 1) != is_and:
            return s, i
    return last


def _leaves(node, dumps, pos, top):
    """Match `node` against the operand list `dumps` starting at pos[0]; False if it is not made of exactly those."""
    if not top and pos[0] < len(dumps) and ast.dump(node) == dumps[pos[0]]:
        pos[0] += 1
        return True
    if isinstance(node, ast.BoolOp):
        return all(_leaves(v, dumps, pos, False) for v in node.values)
    return False


def _same_operands(x, y):
    dumps = [ast.dump(v) for v in x.values]
    pos = [0]
    return _leaves(y, dumps, pos, True) and pos[0] == len(dumps)


def _formula(node, dumps, states, pos, top):
    """(truthiness, index of the operand whose value is the result) of an and/or formula over recorded operand
    states, with Python's short-circuit rules; None when an operand that would be needed was not observed."""
    if not top and pos[0] < len(dumps) and ast.dump(node) == dumps[pos[0]]:
        i = pos[0]
        pos[0] += 1
        return None if states[i] > 1 else (states[i], i)
    is_and, res = isinstance(node.op, ast.And), None
    for k, v in enumerate(node.values):
        if res is not None and (res[0] == 1) != is_and:
            _skip(v, dumps, pos)                 # short-circuited: not evaluated
            continue
        res = _formula(v, dumps, states, pos, False)
        if res is None:
            return None
    return res


def _skip(node, dumps, pos):
    if pos[0] < len(dumps) and ast.dump(node) == dumps[pos[0]]:
        pos[0] += 1
    elif isinstance(node, ast.BoolOp):
        for v in node.values:
            _skip(v, dumps, pos)


def touched(rel, old_src, new_src, parse=ast.parse, lines=None):
    """(mask of tests that may behave differently, mask of tests the recorder has data for, description) or None
    when the edit is not a one-condition edit this module understands."""
    d = data()
    table = d.get("sites", {}).get(rel)
    if not table:
        return None
    try:
        a, b = parse(old_src), parse(new_src)
    except SyntaxError:
        return None
    pair = _diff(a, b, lines)
    if pair is None:
        return None
    x, y = pair
    if not hasattr(x, "lineno"):
        return None
    obs = d["obs"]

    def site(node, kind):
        s = table.get((node.lineno, node.col_offset, node.end_lineno, node.end_col_offset, kind))
        return s

    def ran_mask(g):
        m = 0
        for mask in obs.get(g, {}).values():
            m |= mask
        return m

    hit, what = 0, None
    if isinstance(x, ast.Compare) and isinstance(y, ast.Compare) and len(x.ops) == 1 and len(y.ops) == 1 \
            and ast.dump(x.left) == ast.dump(y.left) and ast.dump(x.comparators[0]) == ast.dump(y.comparators[0]):
        s = site(x, "cmp")
        if not s:
            return None
        o, n = type(x.ops[0]), type(y.ops[0])
        fam = 0 if o in (ast.Eq, ast.NotEq, ast.Is, ast.IsNot) else 1 if o in (ast.Lt, ast.LtE, ast.Gt, ast.GtE) else 2
        for c, mask in obs.get(s[0], {}).items():
            if fam == 2 or c >= 1000:
                hit |= mask
                continue
            vo, vn = _cmp_value(o, fam, c), _cmp_value(n, fam, c)
            if vo is None or vn is None or vo != vn:
                hit |= mask
        what = f"{o.__name__}->{n.__name__}"
    elif isinstance(x, ast.BoolOp) and isinstance(y, ast.BoolOp) and _same_operands(x, y):
        # the same operands in the same order, joined by a different mix of and/or
        s = site(x, "bool")
        if not s:
            return None
        n_ops = s[2]
        dumps = [ast.dump(v) for v in x.values]
        boolean = _bool_context(x, _parents(a))
        for c, mask in obs.get(s[0], {}).items():
            if c >= 1000:
                hit |= mask
                continue
            code, same = c // 3, c % 3
            states = [(code >> (2 * (n_ops - 1 - i))) & 3 for i in range(n_ops)]
            old, new = _formula(x, dumps, states, [0], True), _formula(y, dumps, states, [0], True)
            if old is None or new is None:
                hit |= mask
            elif boolean:
                if old[0] != new[0]:
                    hit |= mask
            elif old[1] != new[1] and not (n_ops == 2 and same == 1):
                hit |= mask
        what = "and/or changed" + (" (truth)" if boolean else " (value)")
    elif isinstance(x, ast.UnaryOp) and isinstance(x.op, ast.Not) and ast.dump(x.operand) == ast.dump(y):
        s = site(x, "not")
        if not s:
            return None
        hit = ran_mask(s[0])
        what = "not removed"
    elif isinstance(y, ast.UnaryOp) and isinstance(y.op, ast.Not) and ast.dump(y.operand) == ast.dump(x):
        s = (site(x, "cmp") if isinstance(x, ast.Compare) else site(x, "bool") if isinstance(x, ast.BoolOp)
             else site(x, "not") if isinstance(x, ast.UnaryOp) else None)
        if not s:
            return None
        hit = ran_mask(s[0])
        what = "not added"
    else:
        return None
    return hit, d.get("ran", 0), what
