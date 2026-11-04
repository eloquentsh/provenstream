# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The streams in one SQLite file: the default store, with the standard library only.

The same tables and the same rules as Postgres (store.py, `PG_SCHEMA`), enforced the same way, by the database: events
and their index are append-only (triggers refuse UPDATE and DELETE), a principal has at most one live token (a partial unique index). The SQL of the shared methods is the base
class's; its `%s` placeholders become SQLite's `?` here.

Compare-and-set: each transaction starts with `BEGIN IMMEDIATE`, which takes the file's write lock before the count is
read, so no other writer (another thread, or another process on the same file: a local command beside `serve`) can
append between the count and the insert. Waiting for that lock is bounded by `busy_timeout`. The file is in WAL mode,
so reads do not wait for writes, with `synchronous=FULL`, so a committed batch (whose receipts were answered) survives
a power loss.

One connection serves every thread of the host, behind a lock (the service's threads take turns, as they do on
Postgres's one connection). A commit here either returns or raises in this process, so there is no lost COMMIT reply
to wait out as on Postgres.
"""
from __future__ import annotations
import os, sqlite3, threading
from typing import Any, List, Sequence

from .store import StreamStore

DEFAULT_PATH = os.path.join("~", ".provenstream", "streams.db")
BUSY_TIMEOUT_MS = 30000

SQLITE_SCHEMA = [
    """CREATE TABLE IF NOT EXISTS events (
         stream_id TEXT NOT NULL, seq INTEGER NOT NULL, request TEXT NOT NULL, event TEXT NOT NULL,
         idem TEXT NOT NULL UNIQUE, accepted_at TEXT NOT NULL, meta_salt BLOB, chain BLOB, PRIMARY KEY (stream_id, seq))""",
    """CREATE TRIGGER IF NOT EXISTS events_append_only_update BEFORE UPDATE ON events
         BEGIN SELECT RAISE(ABORT, 'events are append-only'); END""",
    """CREATE TRIGGER IF NOT EXISTS events_append_only_delete BEFORE DELETE ON events
         BEGIN SELECT RAISE(ABORT, 'events are append-only'); END""",
    """CREATE TABLE IF NOT EXISTS snapshots (
         stream_id TEXT NOT NULL, k INTEGER NOT NULL, state TEXT NOT NULL, prefix_hash TEXT NOT NULL,
         taken_at TEXT NOT NULL, revision TEXT NOT NULL DEFAULT '', PRIMARY KEY (stream_id, k))""",
    """CREATE TABLE IF NOT EXISTS tokens (
         token_hash TEXT PRIMARY KEY, principal TEXT NOT NULL, issued_at TEXT NOT NULL, revoked_at TEXT)""",
    "CREATE INDEX IF NOT EXISTS tokens_principal ON tokens (principal)",
    # a principal is an id and its tokens: no kind (a file from before kept one, defaulted: its checks go)
    "DROP TRIGGER IF EXISTS tokens_kind_fixed_update",
    "DROP TRIGGER IF EXISTS tokens_kind_fixed_insert",
    # one live token per principal: two rotations at once cannot both leave theirs live (the loser runs again)
    "CREATE UNIQUE INDEX IF NOT EXISTS tokens_one_live ON tokens (principal) WHERE revoked_at IS NULL",
    """CREATE TABLE IF NOT EXISTS usage (
         scope TEXT NOT NULL, key TEXT NOT NULL, received INTEGER NOT NULL DEFAULT 0, accepted INTEGER NOT NULL DEFAULT 0,
         events INTEGER NOT NULL DEFAULT 0, bytes INTEGER NOT NULL DEFAULT 0, engine_ms INTEGER NOT NULL DEFAULT 0,
         cpu_ms INTEGER NOT NULL DEFAULT 0, last_active TEXT NOT NULL, PRIMARY KEY (scope, key))""",
    # the event index (store.py's docstring): one row per event at its position in append order (the rowid)
    """CREATE TABLE IF NOT EXISTS event_index (
         pos INTEGER PRIMARY KEY, revision TEXT NOT NULL, stream_id TEXT NOT NULL, seq INTEGER NOT NULL,
         name TEXT NOT NULL, UNIQUE (stream_id, seq))""",
    "CREATE INDEX IF NOT EXISTS event_index_revision ON event_index (revision, pos)",
    "CREATE INDEX IF NOT EXISTS event_index_name ON event_index (revision, name, pos)",
    """CREATE TRIGGER IF NOT EXISTS event_index_append_only_update BEFORE UPDATE ON event_index
         BEGIN SELECT RAISE(ABORT, 'the event index is append-only'); END""",
    """CREATE TRIGGER IF NOT EXISTS event_index_append_only_delete BEFORE DELETE ON event_index
         BEGIN SELECT RAISE(ABORT, 'the event index is append-only'); END""",
]


def sqlite_path(target: str) -> str:
    """The file (or `:memory:`) a SQLite target names (store.open_store lists the forms)."""
    t = target.strip()
    if t.startswith("sqlite:"):
        rest = t[len("sqlite:"):]
        if rest.startswith("//"):
            rest = rest[2:]                    # sqlite://rel/path; sqlite:///abs/path keeps its leading slash
            if rest.startswith("/:memory:"):
                rest = rest[1:]
        if rest.startswith("//"):
            rest = "/" + rest.lstrip("/")      # sqlite:////abs/path, as some tools write it
    else:
        rest = t
    if not rest:
        raise ValueError("%r names no SQLite file (sqlite:///abs/path.db, sqlite://rel/path.db or "
                         "sqlite:///:memory:)" % target)
    return rest if rest == ":memory:" else os.path.expanduser(rest)


def default_target() -> str:
    """The store of `serve` and the other local-only commands when nothing names one: ~/.provenstream/streams.db."""
    return "sqlite:///" + os.path.expanduser(DEFAULT_PATH).lstrip("/")


class SqliteStore(StreamStore):
    """One SQLite file (or `:memory:`). A missing parent directory is created, readable by its owner only (0700): the
    file holds token hashes."""

    OCTETS = "length(CAST(%s AS BLOB))"     # octet_length only exists from SQLite 3.43
    ORDER_OF_APPEND = "e.rowid"             # the events table's rowid is the order rows were appended, exactly

    def __init__(self, path: str):
        self.path = path
        if path != ":memory:":
            parent = os.path.dirname(os.path.abspath(path))
            if not os.path.isdir(parent):
                os.makedirs(parent, mode=0o700)
        self.lock = threading.RLock()
        self.conn = sqlite3.connect(path, timeout=BUSY_TIMEOUT_MS / 1000, isolation_level=None,
                                    check_same_thread=False)
        with self.lock:
            self.conn.execute("PRAGMA busy_timeout = %d" % BUSY_TIMEOUT_MS)
            if path != ":memory:" and self.conn.execute("PRAGMA journal_mode").fetchone()[0].lower() != "wal":
                self.conn.execute("PRAGMA journal_mode = WAL")      # once per file: it needs the file to itself
            self.conn.execute("PRAGMA synchronous = FULL")
            self.conn.execute("BEGIN IMMEDIATE")
            try:
                for stmt in SQLITE_SCHEMA:
                    self.conn.execute(stmt)
                self.conn.execute("COMMIT")
            except BaseException:
                self.conn.execute("ROLLBACK")
                raise
            self._backfill_index()

    @staticmethod
    def _sql(sql: str) -> str:
        return sql.replace("%s", "?")

    def close(self) -> None:
        with self.lock:
            self.conn.close()

    def _run(self, sql: str, args: Sequence[Any] = ()) -> List[tuple]:
        cur = self.conn.execute(self._sql(sql), tuple(args))
        return cur.fetchall() if cur.description else []

    def _exec(self, sql, args=()):
        with self.lock:
            return self._run(sql, args)

    def _tx(self, body):
        """Run `body(exec)` in one `BEGIN IMMEDIATE` transaction: committed if it answers anything but False, rolled
        back (and False answered) if it answers False, rolled back and re-raised if it raises."""
        with self.lock:
            self.conn.execute("BEGIN IMMEDIATE")
            try:
                out = body(self._run)
                if out is False:
                    self.conn.execute("ROLLBACK")
                    return False
                self.conn.execute("COMMIT")
                return out
            except BaseException:
                if self.conn.in_transaction:
                    self.conn.execute("ROLLBACK")
                raise

    def _unique_violation(self, x):
        return isinstance(x, sqlite3.IntegrityError) and "UNIQUE constraint failed" in str(x)
