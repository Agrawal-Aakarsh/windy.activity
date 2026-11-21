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


class InProcessPool:
    """Runs pool work in this process (with the same pickle round trip) to avoid spawning workers."""
    def __init__(self, max_workers=None, mp_context=None, initializer=None, initargs=()):
        if initializer:
            initializer(*pickle.loads(pickle.dumps(initargs)))
    def submit(self, fn, *a, **k):
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
    def __init__(self, wfd=None, stop=False):
        self.failed, self.passed, self.collect = set(), set(), set()
        self.wfd, self.stop = wfd, stop
    def quit(self):
        # the caller only needs to know that something failed: answer now instead of finishing the test
        out = {"rc": 1, "failed": sorted(self.failed), "collect": sorted(self.collect), "passed": [], "early": True}
        os.write(self.wfd, json.dumps(out).encode())
        os._exit(0)
    def pytest_runtest_logstart(self, nodeid, location):
        PROBE["cur"] = nodeid
    def pytest_runtest_logreport(self, report):
        if report.failed:
            self.failed.add(report.nodeid)
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
            if filename in keep:
                for i, rec in enumerate(_o(filename)):
                    if i in keep[filename]:
                        yield rec
                return
            yield from _o(filename)
        setattr(H, fname, wrapped)


def child(req, wfd):
    devnull = os.open(os.devnull, os.O_WRONLY)
    os.dup2(devnull, 1); os.dup2(devnull, 2)
    if req.get("op") in ("state", "baseline"):
        state_child(req, wfd)
    if req.get("probe"):
        install_probe(req["probe"])
    if req.get("slice"):
        try:
            install_slice(req["slice"])
        except BaseException:           # helpers cannot be imported: report as a crash, the caller keeps everything
            os.write(wfd, json.dumps({"rc": -1, "failed": [], "collect": [], "passed": [], "crash": True}).encode())
            os._exit(0)
    plug = Plug(wfd, bool(req.get("stop", True)))
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
           "passed": sorted(plug.passed - plug.failed),
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
