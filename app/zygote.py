"""Warm test runner. Imports the heavy third-party modules once, then forks one child per request.
Each child imports sqlglot from the (patched) working copy and runs the requested tests with pytest.
Protocol: one JSON object per line on stdin -> one JSON object per line on the result fd (argv[2])."""
import json
import os
import signal
import sys
import time

WC = sys.argv[1]
RES = os.fdopen(int(sys.argv[2]), "w")
os.environ["SKIP_INTEGRATION"] = "0"
os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
sys.dont_write_bytecode = True
sys.path.insert(0, WC)
os.chdir(WC)

import concurrent.futures as cf
import concurrent.futures.process as cfp
import pickle
import unittest  # noqa
from concurrent.futures import Future

import pytest

for mod in ("duckdb", "pandas", "numpy"):
    try:
        __import__(mod)
    except Exception:
        pass

try:
    sys.path.insert(1, os.path.dirname(os.path.abspath(__file__)))
    import duckmemo                      # answers DuckDB queries already seen at the pinned commit from a memo
except Exception:
    duckmemo = None


LAZY = [False]


class LazyFuture(Future):
    """Pool work that is done when its result is first asked for (same pickle round trip). A test that reads its
    futures one by one then checks each piece of work right after doing it, so a failing run can stop early."""
    def __init__(self, fn, a, k):
        super().__init__()
        self._job = (fn, a, k)

    def result(self, timeout=None):
        if self._job is not None:
            fn, a, k = self._job
            self._job = None
            try:
                a2, k2 = pickle.loads(pickle.dumps((a, k)))
                self.set_result(pickle.loads(pickle.dumps(fn(*a2, **k2))))
            except BaseException as e:
                self.set_exception(e)
        return super().result(timeout)


class InProcessPool:
    """Runs pool work in this process (with the same pickle round trip) to avoid spawning workers."""
    def __init__(self, max_workers=None, mp_context=None, initializer=None, initargs=()):
        if initializer:
            initializer(*pickle.loads(pickle.dumps(initargs)))
    def submit(self, fn, *a, **k):
        if LAZY[0]:
            return LazyFuture(fn, a, k)
        f = Future()
        try:
            a2, k2 = pickle.loads(pickle.dumps((a, k)))
            f.set_result(pickle.loads(pickle.dumps(fn(*a2, **k2))))
        except BaseException as e:
            f.set_exception(e)
        return f
    def shutdown(self, *a, **k): pass
    def __enter__(self): return self
    def __exit__(self, *a): return False


cf.ProcessPoolExecutor = InProcessPool
cfp.ProcessPoolExecutor = InProcessPool


class Plug:
    def __init__(self, wfd=None, stop=False, max_sub=0):
        self.max_sub = max_sub
        self.failed, self.passed, self.collect = set(), set(), set()
        self.sub, self.whole = [], set()
        self.wfd, self.stop = wfd, stop
    def quit(self):
        # the caller only needs to know that something failed: answer now instead of finishing the test
        out = {"rc": 1, "failed": sorted(self.failed), "collect": sorted(self.collect), "passed": [], "early": True,
               "sub": self.sub, "whole": sorted(self.whole)}
        os.write(self.wfd, json.dumps(out).encode())
        os._exit(0)
    def pytest_runtest_logstart(self, nodeid, location):
        PROBE["cur"] = nodeid
    def pytest_runtest_logreport(self, report):
        if report.failed:
            self.failed.add(report.nodeid)
            msg = getattr(getattr(report, "context", None), "msg", None)
            if msg is not None:
                self.sub.append([report.nodeid, str(msg)[:200]])     # which subtest (fixture record) failed
                if self.max_sub and len(self.sub) > self.max_sub:
                    self.quit()                                       # too many to be worth narrowing down
            elif getattr(report, "when", "call") == "call":
                self.whole.add(report.nodeid)                        # the test itself failed outside any subtest
            if self.stop:
                self.quit()
        elif report.when == "call" and report.passed and type(report).__name__ == "TestReport":
            self.passed.add(report.nodeid)
    def pytest_collectreport(self, report):
        if report.failed:
            self.collect.add(report.nodeid)
            if self.stop:
                self.quit()


PIN = None


def state_child(req, wfd):
    os.dup2(os.open(os.devnull, os.O_WRONLY), 2)
    """Import the patched sqlglot completely and report which import-time state items differ from the pinned commit."""
    try:
        import fingerprint
        failed = [] if req["op"] == "state" else None
        snap = fingerprint.snapshot(fingerprint.load_all(failed))
        if req["op"] == "baseline":
            os.write(wfd, json.dumps({"ok": True, "snap": snap}).encode())
            os._exit(0)
        skip = set(PIN["unstable"])
        pin = PIN["snap"]
        dead = tuple(m + ":" for m in failed)
        changed = [k for k in set(pin) | set(snap) if pin.get(k) != snap.get(k) and k not in skip and not k.startswith(dead)]
        out = {"ok": True, "n": len(changed), "changed": sorted(changed)[:400], "failed_modules": sorted(set(failed))}
    except BaseException as e:      # noqa
        out = {"ok": False, "error": type(e).__name__}
    os.write(wfd, json.dumps(out).encode())
    os._exit(0)


PROBE = {"n": 0, "agree": True, "tests": set(), "cur": None}


def install_probe(spec):
    """Side-by-side evaluation of a changed comparison. `spec` names a line of a patched file and the two operand
    expressions of a comparison whose operator the patch changed. Every time that line runs, both the old and the new
    operator are applied to the live operand values, and also to nearby inputs (each operand against itself and against
    a copy of itself). If the two operators ever disagree, the change is observable."""
    import copy
    import operator as op
    ops = {"Is": op.is_, "IsNot": op.is_not, "Eq": op.eq, "NotEq": op.ne, "Lt": op.lt, "LtE": op.le, "Gt": op.gt,
           "GtE": op.ge, "In": lambda a, b: a in b, "NotIn": lambda a, b: a not in b}
    f_old, f_new = ops[spec["old"]], ops[spec["new"]]
    left = compile(spec["left"], "<left>", "eval"); right = compile(spec["right"], "<right>", "eval")
    suffix, line = os.sep + spec["file"], spec["line"]
    mon = sys.monitoring
    tool = mon.PROFILER_ID

    def same(a, b):
        try:
            x = f_old(a, b)
        except Exception as e:
            x = ("raised", type(e))
        try:
            y = f_new(a, b)
        except Exception as e:
            y = ("raised", type(e))
        return type(x) is type(y) and (x is y or x == y)

    def clone(v):
        try:
            return copy.copy(v)
        except Exception:
            return v

    def on_line(code, lineno):
        if lineno != line or not code.co_filename.endswith(suffix):
            return mon.DISABLE
        frame = sys._getframe(1)
        PROBE["n"] += 1
        PROBE["tests"].add(PROBE["cur"])
        if not PROBE["agree"]:
            return None
        try:
            a = eval(left, frame.f_globals, frame.f_locals); b = eval(right, frame.f_globals, frame.f_locals)
            if spec.get("const") == "right":       # compared against a literal: the literal side cannot vary
                ok = same(a, b) and same(b, b)
            elif spec.get("const") == "left":
                ok = same(a, b) and same(a, a)
            else:
                ok = same(a, b) and same(a, a) and same(b, b) and same(a, clone(a)) and same(b, clone(b))
        except Exception:
            ok = False
        if not ok:
            PROBE["agree"] = False
        return None

    mon.use_tool_id(tool, "blast-radius-probe")
    mon.register_callback(tool, mon.events.LINE, on_line)
    mon.set_events(tool, mon.events.LINE)


def install_slice(spec):
    """Make the test helpers' fixture loaders yield only some records.
    {"files": {name: [indexes]}}: only those records of those files (other files untouched).
    {"changed": pristine_fixture_dir}: only records that differ from the pinned commit's copy, for every file
    (an unchanged file yields nothing). If the number of records changed, the whole file is yielded."""
    import tests.helpers as H
    keep = {k: set(v) for k, v in (spec.get("files") or {}).items()}
    order = {k: list(v) for k, v in (spec.get("ordered") or {}).items()}     # these records, in exactly this order
    pristine = spec.get("changed")
    for fname in ("load_sql_fixtures", "load_sql_fixture_pairs"):
        orig = getattr(H, fname)
        def wrapped(filename, _o=orig):
            if pristine:
                new = list(_o(filename))
                saved = H.FIXTURES_DIR
                H.FIXTURES_DIR = pristine
                try:
                    old = list(_o(filename))
                finally:
                    H.FIXTURES_DIR = saved
                if len(old) != len(new):
                    yield from new
                    return
                for a, b in zip(old, new):
                    if a != b:
                        yield b
                return
            if filename in order:
                recs = list(_o(filename))
                for i in order[filename]:
                    if i < len(recs):
                        yield recs[i]
                return
            if filename in keep:
                for i, rec in enumerate(_o(filename)):
                    if i in keep[filename]:
                        yield rec
                return
            yield from _o(filename)
        setattr(H, fname, wrapped)


def _fast_multiline(self, first, second, msg=None):
    """Same verdict as unittest's assertMultiLineEqual, without building the line-by-line diff text."""
    self.assertIsInstance(first, str, "First argument is not a string")
    self.assertIsInstance(second, str, "Second argument is not a string")
    if first != second:
        self.fail(msg or "strings differ")


unittest.TestCase.assertMultiLineEqual = _fast_multiline


def tree_print(e, out):
    """A complete structural description of a syntax tree (node classes, every argument in order, types, comments,
    meta). It only reads plain attributes, so it does not depend on any sqlglot code a patch could change."""
    args = getattr(e, "args", None)
    if isinstance(args, dict) and hasattr(e, "arg_key"):
        out.append("<" + type(e).__name__)
        for k, v in args.items():
            out.append(k + "=")
            tree_print(v, out)
        t = getattr(e, "_type", None)
        if t is not None:
            out.append("type=")
            tree_print(t, out)
        c = getattr(e, "comments", None)
        if c:
            out.append("comments=" + repr(c))
        m = getattr(e, "_meta", None)
        if m:
            out.append("meta=" + repr(sorted(m.items(), key=repr)))
        out.append(">")
    elif isinstance(e, (list, tuple)):
        out.append("[")
        for x in e:
            tree_print(x, out)
        out.append("]")
    elif isinstance(e, dict):
        out.append("{")
        for k in sorted(e, key=repr):
            out.append(repr(k) + ":")
            tree_print(e[k], out)
        out.append("}")
    elif isinstance(e, (set, frozenset)):
        out.append("set" + repr(sorted(map(repr, e))))
    else:
        out.append(repr(e) + ",")


class _StopAfterOptimize(BaseException):
    pass


def opt_child(req, wfd):
    """For the given records of a fixture: do what the executor test does with each query up to and including the
    optimizer step (the same functions the test calls), and report a fingerprint of the optimized tree."""
    import hashlib
    out = {"ok": False}
    t0 = time.process_time()
    try:
        import sqlglot.executor as X
        import tests.test_executor as TE
        import tests.helpers as H
        schema = getattr(TE, req["schema"])
        got = []
        real = X.optimize

        def stub(*a, **k):
            got.append(real(*a, **k))
            raise _StopAfterOptimize()

        X.optimize = stub

        class Tables(dict):
            def __missing__(self, key):
                return []

        TE.initializer(schema, Tables())
        recs = list(H.load_sql_fixture_pairs(req["fx"]))
        fps, cpu = {}, {}
        for i in req["records"]:
            t1 = time.process_time()
            if i >= len(recs):
                fps[i] = "missing"
                continue
            meta, sql, _ = recs[i]
            del got[:]
            try:
                expr = pickle.loads(pickle.dumps(TE.parse_one(sql)))
                r = TE.mp_execute(expr, meta)
                fps[i] = "none" if r is None else "returned"
            except _StopAfterOptimize:
                parts = []
                tree_print(got[-1], parts)
                fps[i] = hashlib.blake2b("".join(parts).encode(), digest_size=10).hexdigest()
            except BaseException as e:
                fps[i] = "raised:" + type(e).__name__
            cpu[i] = round(time.process_time() - t1, 4)
        out = {"ok": True, "fps": fps, "rec_cpu": cpu}
    except BaseException as e:
        out = {"ok": False, "error": repr(e)[:300]}
    out["cpu"] = round(time.process_time() - t0, 3)
    os.write(wfd, json.dumps(out).encode())
    os._exit(0)


def child(req, wfd):
    LAZY[0] = bool(req.get("lazy"))
    if duckmemo is not None and not req.get("duck", True):
        duckmemo.ON = False
    devnull = os.open(os.devnull, os.O_WRONLY)
    os.dup2(devnull, 1); os.dup2(devnull, 2)
    if req.get("op") in ("state", "baseline"):
        state_child(req, wfd)
    if req.get("op") == "opt":
        opt_child(req, wfd)
    if req.get("probe"):
        install_probe(req["probe"])
    if req.get("slice"):
        try:
            install_slice(req["slice"])
        except BaseException:           # helpers cannot be imported: report as a crash, the caller keeps everything
            os.write(wfd, json.dumps({"rc": -1, "failed": [], "collect": [], "passed": [], "crash": True}).encode())
            os._exit(0)
    plug = Plug(wfd, bool(req.get("stop", True)), int(req.get("max_sub", 0)))
    args = list(req["ids"]) + ["-p", "no:cacheprovider", "-q", "--assert=plain"]
    if req.get("stop", True):
        args.append("-x")
    if req.get("collect_only"):
        args.append("--collect-only")       # only check that every requested test can still be imported and found
    try:
        rc = int(pytest.main(args, plugins=[plug]))
    except BaseException as e:      # noqa
        rc = 99
    out = {"rc": rc, "failed": sorted(plug.failed), "collect": sorted(plug.collect),
           "passed": sorted(plug.passed - plug.failed), "sub": plug.sub, "whole": sorted(plug.whole),
           "probe": {"n": PROBE["n"], "agree": PROBE["agree"], "tests": len(PROBE["tests"] - {None})}}
    os.write(wfd, json.dumps(out).encode())
    os._exit(0)


sys.path.insert(1, os.path.dirname(os.path.abspath(__file__)))
for line in sys.stdin:
    req = json.loads(line)
    r, w = os.pipe()
    t0 = time.time()
    pid = os.fork()
    if pid == 0:
        os.close(r)
        child(req, w)
    os.close(w)
    limit = req.get("limit", 60)
    data, status = b"", None
    signal.signal(signal.SIGALRM, lambda *a: os.kill(pid, signal.SIGKILL))
    signal.setitimer(signal.ITIMER_REAL, limit)
    with os.fdopen(r, "rb") as fh:
        data = fh.read()
    _, status, ru = os.wait4(pid, 0)
    signal.setitimer(signal.ITIMER_REAL, 0)
    try:
        out = json.loads(data)
    except Exception:
        out = {"rc": -1, "failed": [], "collect": [], "passed": [], "crash": True}
    if req.get("op") == "baseline" and out.get("ok"):
        # the pinned commit's import-time state, taken in this same process family so it is comparable
        try:
            unstable = json.load(open(sys.argv[3]))
        except Exception:
            unstable = []
        PIN = {"snap": out.pop("snap"), "unstable": unstable}
        out["items"] = len(PIN["snap"])
    out["secs"] = round(time.time() - t0, 3)
    out["cpu"] = round(ru.ru_utime + ru.ru_stime, 3)
    RES.write(json.dumps(out) + "\n"); RES.flush()
