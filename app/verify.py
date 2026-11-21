"""Run a set of sqlglot tests for real against a patched copy of the pinned checkout.

The working copy is a tree of symlinks into the read-only checkout under /tmp, so only the
patched files are real files. A warm zygote process forks one pytest child per request."""
import json
import os
import subprocess
import sys
from pathlib import Path


class Verifier:
    def __init__(self, sg, tmp="/tmp/br_wc", pin=""):
        self.sg, self.wc = Path(sg), Path(tmp)
        self._farm()
        r, w = os.pipe()
        self.proc = subprocess.Popen(
            [sys.executable, str(Path(__file__).with_name("zygote.py")), str(self.wc), str(w), pin],
            stdin=subprocess.PIPE, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, pass_fds=(w,), text=True)
        os.close(w)
        self.res = os.fdopen(r, "r")
        self.baseline, self.base_cpu, self.last = False, 0, {}

    def _farm(self):
        for top in ("sqlglot", "tests"):
            for d, dirs, files in os.walk(self.sg / top):
                rel = os.path.relpath(d, self.sg)
                os.makedirs(self.wc / rel, exist_ok=True)
                for name in list(dirs):
                    if name == "__pycache__":
                        dirs.remove(name)
                        link = self.wc / rel / name
                        if not link.is_symlink():
                            os.symlink(os.path.join(d, name), link)
                for name in files:
                    link = self.wc / rel / name
                    if not link.is_symlink() and not link.exists():
                        os.symlink(os.path.join(d, name), link)

    def state(self, patched, limit=60):
        """Changed import-state items for this patch, or None when the patched package cannot be imported."""
        if not self.baseline:
            b = self._request({}, {"op": "baseline", "limit": limit})
            self.baseline = bool(b.get("ok"))
            self.base_cpu = b.get("cpu", 0)
            if not self.baseline:
                self.last = b
                return None
        r = self._request(patched, {"op": "state", "limit": limit})
        self.last = r
        if not r.get("ok"):
            return None
        return r

    def run(self, patched, ids, stop=True, limit=60, probe=None, collect_only=False, slice=None, max_sub=0, duck=True):
        """patched: {relative path: new text or None (deleted)}. Returns the zygote's result dict."""
        req = {"ids": ids, "stop": stop, "limit": limit}
        if collect_only:
            req["collect_only"] = True
        if probe:
            req["probe"] = probe
        if slice:
            req["slice"] = slice
        if max_sub:
            req["max_sub"] = max_sub
        if not duck:
            req["duck"] = False
        return self._request(patched, req)

    def _request(self, patched, req):
        touched = []
        try:
            for rel, text in patched.items():
                p = self.wc / rel
                os.makedirs(p.parent, exist_ok=True)
                if p.is_symlink() or p.exists():
                    p.unlink()
                if text is not None:
                    p.write_text(text, encoding="utf-8")
                touched.append(rel)
            self.proc.stdin.write(json.dumps(req) + "\n")
            self.proc.stdin.flush()
            line = self.res.readline()
            return json.loads(line) if line else {"rc": -1, "failed": [], "passed": [], "collect": [], "crash": True}
        finally:
            for rel in touched:
                p = self.wc / rel
                if p.exists() or p.is_symlink():
                    p.unlink()
                src = self.sg / rel
                if src.exists():
                    os.symlink(src, p)

    def close(self):
        try:
            self.proc.stdin.close(); self.proc.wait(timeout=5)
        except Exception:
            self.proc.kill()
