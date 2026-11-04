# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The store suite: every test that takes `store` runs on SQLite and on Postgres (conftest.store_target). The tests that
take `dsn` are about Postgres alone."""
import json, os, stat, threading

import pytest

from conftest import U, pgtmp, raw_sql, refused_by_trigger

from provenstream import chain
from provenstream.store import ImportRefused, is_sqlite, open_store


def row(i, key=None):
    return ({"actor_id": U("ann"), "command": {"command": "x", "n": i}, "fresh": []},
            {"event": "x", "n": i}, key or "k%d" % i)


def chained_rows(stream, n, start=0, head=None, meta=None):
    """`n` rows from `start` with salts and chain heads, as the service writes them."""
    out, h = [], head or chain.genesis(stream)
    for i in range(start, start + n):
        req, ev, key = row(i, "%s-k%d" % (stream, i))
        if meta is not None:
            req["command"]["meta"] = ev["meta"] = meta
        salt = chain.new_salt()
        r, e, _ = chain.redact(req, ev, salt)
        h = chain.link(h, i, r, e)
        out.append((req, ev, key, salt, h))
    return out, h


def test_compare_and_set(store):
    s = U("s")
    assert store.append_batch(s, 0, [row(0), row(1)])
    assert not store.append_batch(s, 1, [row(2)])            # the stream has 2 rows, not 1
    assert store.length(s) == 2
    assert store.append_batch(s, 2, [row(2)])
    assert [r[0] for r in store.read(s)] == [0, 1, 2]
    assert store.find_idem("k1")[:2] == (s, 1)
    assert not store.append_batch(U("t"), 0, [row(9, "k1")])  # a stored key: nothing stored
    assert store.length(U("t")) == 0


def test_compare_and_set_from_two_connections(store, store_target):
    """Two stores on one database (two hosts, or a local command beside `serve`): every append lands once, in one
    order, whichever connection made it."""
    other = open_store(store_target)
    s, won = U("s"), []
    try:
        def writer(st, tag):
            for i in range(20):
                while True:
                    n = st.length(s)
                    if st.append_batch(s, n, [row(n, "%s-%d" % (tag, i))]):
                        won.append(tag)
                        break
        ts = [threading.Thread(target=writer, args=(st, tag)) for st, tag in ((store, "a"), (other, "b"))]
        [t.start() for t in ts]
        [t.join() for t in ts]
    finally:
        other.close()
    assert [r[0] for r in store.read(s)] == list(range(40)) and sorted(won) == ["a"] * 20 + ["b"] * 20


def test_events_are_append_only(store, store_target):
    s = U("s")
    store.append_batch(s, 0, [row(0)])
    with pytest.raises(refused_by_trigger(store_target)):
        raw_sql(store_target, "UPDATE events SET event = '{}'")
    with pytest.raises(refused_by_trigger(store_target)):
        raw_sql(store_target, "DELETE FROM events")
    assert store.length(s) == 1


def test_tokens(store, store_target):
    """A principal is an id and its tokens: one live token, rotated; an id is issued a first token once."""
    p = U("p")
    t = store.create_principal(p)
    assert store.principal_of(t) == p and store.known(p) and not store.known(U("q"))
    t2 = store.rotate(p)
    assert store.principal_of(t) is None and store.principal_of(t2) == p
    with pytest.raises(ValueError):
        store.create_principal(p)
    with pytest.raises(Exception):
        raw_sql(store_target, "INSERT INTO tokens (token_hash, principal, issued_at) VALUES ('h', %s, 'now')", (p,))


def test_a_store_from_before_kinds_opens(tmp_path):
    """A SQLite file made when principals had kinds (a kind column and its triggers) opens, and issues tokens."""
    import sqlite3
    path = str(tmp_path / "old.db")
    c = sqlite3.connect(path)
    c.executescript("""
        CREATE TABLE tokens (token_hash TEXT PRIMARY KEY, principal TEXT NOT NULL, issued_at TEXT NOT NULL,
          revoked_at TEXT, kind TEXT NOT NULL DEFAULT 'person' CHECK (kind IN ('person', 'agent')));
        INSERT INTO tokens VALUES ('x', 'a', 'then', NULL, 'agent');
        CREATE TRIGGER tokens_kind_fixed_insert BEFORE INSERT ON tokens
          WHEN EXISTS (SELECT 1 FROM tokens WHERE principal = NEW.principal AND kind <> NEW.kind)
          BEGIN SELECT RAISE(ABORT, 'a principal''s kind is never changed'); END;""")
    c.close()
    s = open_store("sqlite:///" + path.lstrip("/"))
    try:
        s._exec("UPDATE tokens SET revoked_at = 'now'")
        assert s.principal_of(s.rotate("a")) == "a"
    finally:
        s.close()


def test_usage_counters_add(store):
    store.bump_usage([("stream", "s", {"received": 2, "accepted": 1, "events": 1, "bytes": 10, "engine_ms": 3.4})])
    store.bump_usage([("stream", "s", {"received": 1}), ("revision", "r", {"cpu_ms": 7})])
    u = {(r["scope"], r["key"]): r for r in store.usage()}
    assert u[("stream", "s")]["received"] == 3 and u[("stream", "s")]["bytes"] == 10
    assert u[("revision", "r")]["cpu_ms"] == 7 and u[("stream", "s")]["last_active"]


def test_snapshots_and_stored_bytes(store):
    s = U("s")
    store.append_batch(s, 0, [row(0), row(1)])
    store.put_snapshot(s, 2, {"a": "é"}, "r1")
    store.put_snapshot(s, 2, {"a": "other"}, "r1")                      # one snapshot per k: the first stays
    assert [(k, st) for k, st, _ in store.snapshots(s, "r1")] == [(2, {"a": "é"})] and store.snapshots(s, "r2") == []
    store.delete_snapshot(s, 2)
    assert store.latest_snapshot(s, "r1") is None
    assert store.stored_bytes(s) == sum(len(r.encode()) + len(e.encode()) for _, r, e in store.read(s))


def test_export_import_round_trip(store, tmp_path, pg_cluster):
    """Export writes every row with its salt and head; import into another store (of the other kind too) checks every
    chain and stores the rows as they were, legacy rows (no salt, no head) included."""
    s1, s2, legacy = U("s1"), U("s2"), U("legacy")
    rows1, h1 = chained_rows(s1, 3, meta="a secret")
    store.append_batch(s1, 0, rows1)
    rows2, _ = chained_rows(s2, 2)
    store.append_batch(s2, 0, rows2)
    store.append_batch(legacy, 0, [row(0, "l0"), row(1, "l1")])          # written before the chain
    out = str(tmp_path / "streams.export")
    assert store.export(out) == 7
    lines = open(out, encoding="utf-8").read().splitlines()
    assert json.loads(lines[0]) == {"provenstream_export": 2}
    got = {(d["stream_id"], d["seq"]): d for d in map(json.loads, lines[1:])}
    first = got[(s1, 0)]
    assert set(first) == {"stream_id", "seq", "request", "event", "meta_salt", "chain", "idem", "accepted_at"}
    assert isinstance(first["request"], str) and first["chain"] == rows1[0][4].hex()
    assert first["meta_salt"] == rows1[0][3].hex()
    assert got[(legacy, 1)]["chain"] is None and got[(legacy, 1)]["meta_salt"] is None
    for target in ("sqlite:///:memory:", "sqlite:///" + str(tmp_path / "copy.db").lstrip("/"),
                   pgtmp.create_db(pg_cluster)):
        copy = open_store(target)
        try:
            assert copy.import_export(out) == {s1: 3, s2: 2, legacy: 2}
            for s in (s1, s2, legacy):
                assert copy.read_chained(s) == store.read_chained(s)
            assert copy.streams() == store.streams() and copy.read_chained(s1)[-1][4] == h1
            assert copy.find_idem(rows1[1][2])[:2] == (s1, 1)
            with pytest.raises(ImportRefused, match="already has rows"):
                copy.import_export(out)                                 # never adds to a stream
            assert copy.count() == 7
        finally:
            copy.close()


def test_import_refuses_a_broken_chain(store, tmp_path):
    s = U("s")
    store.append_batch(s, 0, chained_rows(s, 3)[0])
    out = str(tmp_path / "x.export")
    store.export(out)
    lines = open(out, encoding="utf-8").read().splitlines()

    def refused(text, match):
        bad = str(tmp_path / "bad.export")
        open(bad, "w", encoding="utf-8").write(text)
        copy = open_store("sqlite:///:memory:")
        try:
            with pytest.raises(ImportRefused, match=match):
                copy.import_export(bad)
            assert copy.count() == 0                                      # nothing stored
        finally:
            copy.close()
    forged = json.loads(lines[2])
    forged["event"] = forged["event"].replace('"n":1', '"n":7')
    refused("\n".join([lines[0], lines[1], json.dumps(forged)] + lines[3:]) + "\n", "seq 1: the stored head")
    refused("\n".join([lines[0], lines[1], lines[3]]) + "\n", "missing, reordered or repeated")
    refused("\n".join(lines[1:]) + "\n", "not a provenstream export")
    refused("\n".join(lines + ["{nope"]) + "\n", "not JSON")


def test_sqlite_targets(tmp_path, monkeypatch):
    """The SQLite forms of a target; a missing parent directory is made, its owner's only."""
    from provenstream.store_sqlite import default_target, sqlite_path
    assert sqlite_path("sqlite:///abs/x.db") == "/abs/x.db" and sqlite_path("sqlite:////abs/x.db") == "/abs/x.db"
    assert sqlite_path("sqlite://rel/x.db") == "rel/x.db" == sqlite_path("sqlite:rel/x.db") == sqlite_path("rel/x.db")
    assert sqlite_path("sqlite:///:memory:") == ":memory:" == sqlite_path(":memory:")
    assert all(is_sqlite(t) for t in ("sqlite:///a", "x.db", "x.sqlite", "./y/x.sqlite3", ":memory:"))
    assert not any(is_sqlite(t) for t in ("", "postgresql://", "host=h dbname=x.db", "postgresql://h/x.db"))
    monkeypatch.setenv("HOME", str(tmp_path))
    assert default_target() == "sqlite:///" + str(tmp_path / ".provenstream" / "streams.db").lstrip("/")
    s = open_store(default_target())
    try:
        assert s.count() == 0
    finally:
        s.close()
    assert stat.S_IMODE(os.stat(tmp_path / ".provenstream").st_mode) == 0o700


def test_connection_string_forms(dsn, monkeypatch):
    """A libpq connection string in either form opens the store, and an empty one uses libpq's own environment."""
    from psycopg.conninfo import conninfo_to_dict
    d = conninfo_to_dict(dsn)
    keywords = " ".join("%s=%s" % (k, v) for k, v in sorted(d.items()))
    for target in (dsn, keywords):
        s = open_store(target)
        try:
            assert s.count() >= 0
        finally:
            s.close()
    env = {"host": "PGHOST", "port": "PGPORT", "user": "PGUSER", "dbname": "PGDATABASE", "password": "PGPASSWORD"}
    for k, v in d.items():
        monkeypatch.setenv(env[k], v)
    for target in ("", "postgresql://"):
        s = open_store(target)
        try:
            assert s.count() >= 0
        finally:
            s.close()


def opened(stream, commit, package="examples/work", actor=None):
    """A stream.opened event naming the revision `commit/package`."""
    return {"event": "stream.opened", "stream_id": stream, "actor_id": actor or U("ann"), "meta": None,
            "proof_revision_url": "https://example.org/repo/tree/%s/%s" % (commit, package)}


def test_event_index_follows_appends(store, store_target):
    """Every append indexes its events in the same transaction, at positions in append order across streams, with the
    revision from the stream's opening and the event name; a failed compare-and-set indexes nothing; the index is
    append-only."""
    c1, c2 = "1" * 40, "2" * 40
    rev1, rev2 = c1 + "/examples/work", c2 + "/examples/work"
    s1, s2, s3 = U("s1"), U("s2"), U("s3")
    ev = lambda s, name, **f: dict({"event": name, "stream_id": s, "actor_id": U("ann"), "meta": "m" * 100}, **f)
    assert store.append_batch(s1, 0, [({}, opened(s1, c1), "a0")])
    assert store.append_batch(s2, 0, [({}, opened(s2, c1), "b0")])
    assert store.append_batch(s3, 0, [({}, opened(s3, c2), "c0")])
    assert store.append_batch(s1, 1, [({}, ev(s1, "work.asked", preparer_id=U("ben")), "a1"),
                                      ({}, ev(s1, "work.asked", preparer_id=U("cy")), "a2")])
    assert store.append_batch(s2, 1, [({}, ev(s2, "work.asked", preparer_id=U("ben")), "b1")])
    assert not store.append_batch(s2, 1, [({}, ev(s2, "work.asked", preparer_id=U("dee")), "b2")])   # the CAS fails
    assert store.append_batch(s3, 1, [({}, ev(s3, "work.asked", preparer_id=U("ben")), "c1")])
    assert store.count() == 7 == store._exec("SELECT count(*) FROM event_index")[0][0]
    key = lambda rows: [(s, seq) for _, s, seq, _, _ in rows]
    assert key(store.find_events(rev1)) == [(s1, 0), (s2, 0), (s1, 1), (s1, 2), (s2, 1)]       # append order, rev1 only
    assert key(store.find_events(rev2)) == [(s3, 0), (s3, 1)]
    assert key(store.find_events(rev1, name="work.asked")) == [(s1, 1), (s1, 2), (s2, 1)]
    assert key(store.find_events(rev1, name="stream.opened")) == [(s1, 0), (s2, 0)]
    assert key(store.find_events(rev1, name="work.replied")) == [] == key(store.find_events("3" * 40))
    pos = [p for p, *_ in store.find_events(rev1)]
    assert pos == sorted(pos) and key(store.find_events(rev1, after=pos[1])) == [(s1, 1), (s1, 2), (s2, 1)]
    assert key(store.find_events(rev1, after=pos[1], limit=2)) == [(s1, 1), (s1, 2)]
    assert key(store.find_events(rev1, after=pos[-1])) == []
    assert store.find_events(rev1)[2][3] == store.read(s1)[1][2]                                 # the stored event text
    for sql in ("UPDATE event_index SET revision = 'x'", "DELETE FROM event_index"):
        with pytest.raises(refused_by_trigger(store_target)):
            raw_sql(store_target, sql)


def test_event_index_is_backfilled_once_and_moves_with_an_import(store, store_target, tmp_path):
    """A database from before the index gets one at open, from its stored rows in the order they were appended, and a
    later open adds nothing; an import indexes the imported rows."""
    c = "4" * 40
    rev = c + "/examples/work"
    s1, s2 = U("s1"), U("s2")
    ev = lambda s, i: {"event": "x", "stream_id": s, "actor_id": U("ann"), "meta": None, "n": i}
    store.append_batch(s1, 0, [({}, opened(s1, c), "s1-0")])
    store.append_batch(s2, 0, [({}, opened(s2, c), "s2-0")])
    store.append_batch(s1, 1, [({}, ev(s1, 1), "s1-1"), ({}, ev(s1, 2), "s1-2")])
    store.append_batch(s2, 1, [({}, ev(s2, 9), "s2-1")])
    before = store.find_events(rev)
    assert [(s, seq) for _, s, seq, _, _ in before] == [(s1, 0), (s2, 0), (s1, 1), (s1, 2), (s2, 1)]
    store.close()
    raw_sql(store_target, "DROP TABLE event_index")
    again = open_store(store_target)                       # a database from before the index: backfilled at open
    try:
        after = again.find_events(rev)
        same = lambda rows: sorted((s, seq, ev) for _, s, seq, ev, _ in rows)
        assert same(after) == same(before)
        if store_target.startswith("sqlite:"):
            assert after == before                           # SQLite's rowid is the exact order; Postgres orders by
        else:                                                # the time (to the second), then the stream and seq
            assert [seq for _, s, seq, _, _ in after if s == s1] == [0, 1, 2]
        assert again._backfill_index() == 0                 # nothing more to index: idempotent
        assert again.find_events(rev, name="x")[0][1:3] in ((s1, 1), (s2, 1))
        out = str(tmp_path / "streams.export")
        again.export(out)
    finally:
        again.close()
    copy = open_store("sqlite:///:memory:")
    try:
        copy.import_export(out)
        # an export has no positions: the import orders by accepted time, then stream, then seq (here all in one second)
        got = [(s, seq, ev) for _, s, seq, ev, _ in copy.find_events(rev)]
        assert sorted(got) == sorted((s, seq, ev) for _, s, seq, ev, _ in before)
        assert [seq for s, seq, _ in got if s == s2] == [0, 1]
        assert [seq for s, seq, _ in got if s == s1] == [0, 1, 2]
    finally:
        copy.close()
