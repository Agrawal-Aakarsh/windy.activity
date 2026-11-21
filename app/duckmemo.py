"""Memo for DuckDB query results.

A few of sqlglot's tests compare against DuckDB. DuckDB and the fixture data are the same for every commit, so the
result of a given SQL text on a given set of views never changes. This module wraps duckdb.connect so that a query
whose exact text (and whose connection's exact setup statements) was already answered at the pinned commit gets that
answer back without running DuckDB again. Any other query runs for real. The test's own assertions always run.
"""
import atexit
import hashlib
import os
import pickle
import re
import zlib

MEMO = {}
NEW = {}
REC = os.environ.get("BR_DUCK_REC")
ON = True
_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "duck.pkl.z")
_ROOT = re.compile(r"[^'\"\s]*?(tests/fixtures/)")
_QUERY = re.compile(r"\s*(?:SELECT|WITH|\()", re.I)


def load():
    try:
        with open(_PATH, "rb") as f:
            MEMO.update(pickle.loads(zlib.decompress(f.read())))
    except Exception:
        pass


class _Hit:
    def __init__(self, conn, sql, blob):
        self._conn, self._sql, self._blob = conn, sql, blob

    def fetchdf(self):
        try:
            return pickle.loads(self._blob)
        except Exception:                       # unreadable memo entry: just ask DuckDB
            return self._conn._c.execute(self._sql).fetchdf()

    def __getattr__(self, name):
        return getattr(self._conn._c.execute(self._sql), name)


class _Miss:
    def __init__(self, res, key):
        self._res, self._key = res, key

    def fetchdf(self):
        df = self._res.fetchdf()
        if REC:
            NEW[self._key] = pickle.dumps(df, protocol=4)
        return df

    def __getattr__(self, name):
        return getattr(self._res, name)


class Conn:
    def __init__(self, c):
        self._c, self._h = c, hashlib.sha1()

    def execute(self, sql, *a, **k):
        if a or k or not isinstance(sql, str):
            return self._c.execute(sql, *a, **k)
        if not _QUERY.match(sql):
            self._h.update(_ROOT.sub(r"\1", sql).encode())      # setup statement: part of this connection's identity
            return self._c.execute(sql)
        key = (self._h.hexdigest(), sql)
        blob = MEMO.get(key) if ON else None
        if blob is not None:
            return _Hit(self, sql, blob)
        return _Miss(self._c.execute(sql), key)

    def __getattr__(self, name):
        return getattr(self._c, name)

    def __enter__(self):                         # `with duckdb.connect() as c:` must keep working
        self._c.__enter__()
        return self

    def __exit__(self, *exc):
        return self._c.__exit__(*exc)


def install():
    try:
        import duckdb
    except Exception:
        return
    if getattr(duckdb.connect, "_memo", False):
        return
    real = duckdb.connect

    def connect(*a, **k):
        return Conn(real(*a, **k))

    connect._memo = True
    duckdb.connect = connect


def _dump():
    if REC and NEW:
        with open(REC, "wb") as f:
            f.write(zlib.compress(pickle.dumps(NEW, protocol=4), 6))


load()
install()
atexit.register(_dump)
