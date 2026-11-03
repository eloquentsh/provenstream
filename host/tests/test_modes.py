# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The CLI's modes: resolution, mixing errors, every command class in each mode, local writes beside a running host,
`--as`, and `mode`."""
import json, os, subprocess, threading, time

import pytest

from conftest import ROOT, U
from test_client import BIN, host, run  # noqa: F401  (the running-host fixture)

from provenstream import chain, client, mode, wire
from provenstream.client import ClientError


def R(base=None, db=None, actor=None, **env):
    return mode.resolve(base, db, actor, env)


def test_resolution_order():
    assert R(PROVENSTREAM_MODE="remote", PROVENSTREAM_DATABASE_URL="x").mode == "remote"
    assert R(PROVENSTREAM_MODE="local").mode == "local" and R(PROVENSTREAM_MODE="local").db == mode.default_db()
    assert mode.default_db().endswith("/.provenstream/streams.db") and mode.default_db().startswith("sqlite:///")
    # a local-only command with nothing named: local, the default database; with a host named: remote
    r = mode.resolve(None, None, None, {}, local_only=True)
    assert r.mode == "local" and r.db == mode.default_db() and "default database" in r.why
    assert mode.resolve(None, None, None, {"PROVENSTREAM_BASE_URL": "http://h"}, local_only=True).mode == "remote"
    assert mode.resolve(None, None, None, {"PROVENSTREAM_MODE": "remote"}, local_only=True).mode == "remote"
    assert R(db="host=h").why == "--db" and R(db="host=h").mode == "local"
    assert R(PROVENSTREAM_DATABASE_URL="host=h").why == "PROVENSTREAM_DATABASE_URL"
    r = R()
    assert r.mode == "remote" and r.base_url == client.DEFAULT_BASE_URL.rstrip("/")
    assert R(PROVENSTREAM_BASE_URL="http://h:1").base_url == "http://h:1"
    assert R("http://f:2", PROVENSTREAM_BASE_URL="http://h:1").base_url == "http://f:2"
    with pytest.raises(ClientError) as x:
        R(PROVENSTREAM_MODE="cloud")
    assert x.value.exit_code == client.EXIT_MODE


def test_generic_database_settings_never_select_local():
    for env in ({"DATABASE_URL": "postgresql://x@y/z"}, {"PGHOST": "/tmp", "PGDATABASE": "z", "PGUSER": "x"}):
        assert R(**env).mode == "remote"


def test_mixing_is_an_error():
    cases = [dict(base="http://h", db="host=h"),                                   # a base URL in local mode
             dict(db="host=h", PROVENSTREAM_BASE_URL="http://h"),
             dict(PROVENSTREAM_MODE="local", base="http://h"),
             dict(actor=U("ann")),                                                  # --as in remote mode
             dict(db="host=h", PROVENSTREAM_MODE="remote")]                        # --db with remote
    for c in cases:
        with pytest.raises(ClientError) as x:
            R(**c)
        assert x.value.exit_code == client.EXIT_MODE and "rule" in x.value.message, c
    # an explicit remote mode with a base URL is remote, whatever database variable is set
    assert R("http://h", PROVENSTREAM_MODE="remote", PROVENSTREAM_DATABASE_URL="host=h").mode == "remote"


def test_redaction_and_mode_command(dsn, host):
    for target, secret in (("postgresql://u:s3cret@db.example:5432/x", "s3cret"),
                           ("host=db.example user=u password=s3cret dbname=x", "s3cret")):
        p = run("mode", "--db", target)
        assert p.returncode == 0 and secret not in p.stdout and "***" in p.stdout and "local" in p.stdout
    p = run("mode", "--json", env={"PROVENSTREAM_DATABASE_URL": dsn})
    d = json.loads(p.stdout)
    assert d["mode"] == "local" and d["decided_by"] == "PROVENSTREAM_DATABASE_URL"
    d = json.loads(run("mode", "--json", env={"PROVENSTREAM_BASE_URL": host["url"]}).stdout)
    assert d["mode"] == "remote" and d["token"] == "not set"
    d = json.loads(run("mode", "--json", env={"PROVENSTREAM_BASE_URL": host["url"]}, token=host["ann"]["token"]).stdout)
    assert d["token"] == "set" and d["principal"] == {"principal_id": host["ann"]["principal_id"]}
    assert host["ann"]["token"] not in json.dumps(d)


def local(dsn, engines, *args, actor=None):
    env = {"PROVENSTREAM_DATABASE_URL": dsn, "PROVENSTREAM_ENGINES": engines["dir"]}
    extra = ["--as", actor] if actor else []
    return run(*(list(args) + extra), env=env)


def test_local_writes_and_reads(dsn, engines, host):
    ann, cy = host["ann"]["principal_id"], host["cy"]["principal_id"]
    proof = engines["urls"]["tasks"]
    p = local(dsn, engines, "open", proof, "--meta", "local", actor=ann)
    assert p.returncode == 0, p.stderr
    s = json.loads(p.stdout)["event"]["stream_id"]
    p = local(dsn, engines, "call", "task.open", "-f", "stream_id=" + s, "-f", "task_id=" + U("s"), actor=ann)
    assert json.loads(p.stdout)["seq"] == 1 and json.loads(p.stdout)["event"]["actor_id"] == ann   # --as: actor_id
    p = local(dsn, engines, "call", "task.open", json.dumps({"stream_id": s, "task_id": U("t")}), actor=ann)
    assert p.returncode == 0 and len(json.loads(p.stdout)["chain"]) == 64
    p = local(dsn, engines, "call", "task.open", json.dumps({"stream_id": s, "task_id": U("u")}), actor=cy)
    assert p.returncode == client.EXIT_REFUSED and p.stderr == "provenstream: refused: only_opener_can_open_tasks\n"
    p = local(dsn, engines, "close", s, "--yes", actor=U("stranger"))
    assert p.returncode == client.EXIT_UNAUTHORIZED and "no such principal" in p.stderr
    p = local(dsn, engines, "close", s, "--yes")
    assert p.returncode == client.EXIT_UNAUTHORIZED and "--as" in p.stderr
    # reads: the same shape as the host's; reading is unrestricted, so any principal reads, and the operator too
    ev = json.loads(local(dsn, engines, "events", s, actor=cy).stdout)["events"]
    remote_ev = json.loads(run("events", s, env={"PROVENSTREAM_BASE_URL": host["url"]},
                               token=host["ann"]["token"]).stdout)["events"]
    assert ev == remote_ev and all(len(e["chain"]) == 64 for e in ev)
    hd = json.loads(local(dsn, engines, "head", s, actor=ann).stdout)
    assert hd == {"stream_id": s, "length": 3, "chain": ev[-1]["chain"]}
    assert json.loads(local(dsn, engines, "head", s).stdout) == hd                   # the operator, as no one
    p = local(dsn, engines, "mode", actor=ann)
    assert p.returncode == 2 and "--as" in p.stderr                              # mode makes no call
    p = local(dsn, engines, "verify", "--stream", s)
    assert p.returncode == 0 and "3 rows replay" in p.stdout, p.stdout + p.stderr
    revs = json.loads(local(dsn, engines, "revisions").stdout)["revisions"]
    assert {r["revision"] for r in revs} == {engines[k] for k in ("core", "log", "principals", "tasks", "work", "tower")}
    assert not any(r["running"] for r in revs)
    p = local(dsn, engines, "close", s, "--yes", actor=ann)
    assert p.returncode == 0
    # verify --rows in remote mode, with no host at all
    rows = json.loads(run("call", "stream.rows", json.dumps({"stream_id": s}),
                          env={"PROVENSTREAM_BASE_URL": host["url"]}, token=host["ann"]["token"]).stdout)["rows"]
    import tempfile
    with tempfile.NamedTemporaryFile("w", suffix=".jsonl", delete=False) as fh:
        fh.write("".join(json.dumps(dict(r, stream_id=s)) + "\n" for r in rows))
    try:
        p = run("verify", "--rows", fh.name, "--engines", engines["dir"], env={"PROVENSTREAM_BASE_URL": "http://127.0.0.1:9"})
        assert p.returncode == 0 and "4 rows replay" in p.stdout, p.stdout + p.stderr
    finally:
        os.unlink(fh.name)


def test_local_only_commands_in_remote_mode():
    for args in (["serve"], ["host", "principal", "create"], ["token", "rotate", U("x")], ["replay"],
                 ["export", "x"], ["import", "x"]):
        for env in ({"PROVENSTREAM_BASE_URL": "http://127.0.0.1:9"}, {"PROVENSTREAM_MODE": "remote"}):
            p = run(*args, env=env)
            assert p.returncode == client.EXIT_NEEDS_LOCAL and "needs a database" in p.stderr, (args, env)


def test_a_clean_machine_serves_from_the_default_sqlite_file(engines, tmp_path):
    """No database and nothing configured: `host principal create` and `serve` use ~/.provenstream/streams.db (its
    directory made, the owner's only), and the host answers."""
    import site, stat, urllib.request
    from test_client import free_port
    home = {"HOME": str(tmp_path), "PYTHONUSERBASE": site.getuserbase()}     # a new home, the same Python packages
    tf = tmp_path / "ann.token"
    p = run("host", "principal", "create", "--token-file", str(tf), env=home)
    assert p.returncode == 0, p.stderr
    ann = dict(json.loads(p.stdout), token=tf.read_text().strip())
    assert set(json.loads(p.stdout)) == {"principal_id"} and ann["token"] not in p.stdout + p.stderr
    assert stat.S_IMODE(os.stat(tmp_path / ".provenstream").st_mode) == 0o700
    assert (tmp_path / ".provenstream" / "streams.db").exists()
    d = json.loads(run("mode", "--json", "--db", str(tmp_path / "x.db"), env=home).stdout)
    assert d["store"] == "sqlite" and d["mode"] == "local"
    port = free_port()
    e = {k: v for k, v in os.environ.items() if not k.startswith("PROVENSTREAM_")}
    e.update(home)
    srv = subprocess.Popen([BIN, "serve", "--engines", engines["dir"], "--port", str(port)], env=e,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    url = "http://127.0.0.1:%d" % port
    try:
        for _ in range(100):
            try:
                urllib.request.urlopen(url + "/healthz", timeout=1)
                break
            except OSError:
                time.sleep(0.1)
        p = run("open", engines["urls"]["tasks"], env={"PROVENSTREAM_BASE_URL": url}, token=ann["token"])
        assert p.returncode == 0, p.stderr
        assert json.loads(p.stdout)["seq"] == 0
    finally:
        srv.terminate()
        srv.wait(10)


def test_export_from_postgres_import_into_sqlite(dsn, engines, tmp_path):
    """Streams written on Postgres move to a SQLite file: export, import (every chain checked), the same heads, and
    the export file verifies and replays as it is."""
    ann = json.loads(run("host", "principal", "create", "--db", dsn).stdout)["principal_id"]
    proof = engines["urls"]["tasks"]
    streams = []
    for meta in ("first", None):
        p = local(dsn, engines, *(["open", proof] + (["--meta", meta] if meta else [])), actor=ann)
        s = json.loads(p.stdout)["event"]["stream_id"]
        local(dsn, engines, "call", "task.open", "-f", "stream_id=" + s, "-f", "task_id=" + U("first"), actor=ann)
        for i in range(3):
            assert local(dsn, engines, "call", "task.open", json.dumps({"stream_id": s, "task_id": U("t%d" % i),
                                                                        "meta": "m%d" % i}), actor=ann).returncode == 0
        streams.append(s)
    out, db = str(tmp_path / "streams.export"), "sqlite:///" + str(tmp_path / "moved.db").lstrip("/")
    p = run("export", out, "--db", dsn)
    assert p.returncode == 0 and "10 rows" in p.stdout, p.stderr
    p = run("import", out, "--db", db)
    assert p.returncode == 0 and "2 streams, 10 rows" in p.stdout and "tokens are not" in p.stdout, p.stderr
    from provenstream.store import open_store
    moved = open_store(db)
    try:
        moved.create_principal(ann)                  # tokens do not move: ann's is issued again on the new store
    finally:
        moved.close()
    for s in streams:
        assert json.loads(local(db, engines, "head", s, actor=ann).stdout) == \
            json.loads(local(dsn, engines, "head", s, actor=ann).stdout)
        p = run("verify", "--rows", out, "--stream", s, "--engines", engines["dir"])
        assert p.returncode == 0 and "5 rows replay" in p.stdout, p.stdout + p.stderr
    p = run("verify", "--rows", out, "--engines", engines["dir"])
    assert p.returncode == client.EXIT_PARAMS and "--stream" in p.stderr
    p = run("replay", "--db", db, "--engines", engines["dir"])
    assert p.returncode == 0 and "does not replay: none" in p.stdout, p.stdout + p.stderr
    p = run("import", out, "--db", db)
    assert p.returncode == 1 and "REFUSED" in p.stderr and "already has rows" in p.stderr


def test_a_token_for_an_imported_principal(engines, tmp_path):
    """Export, import into a fresh SQLite file, issue the original opener a token for its own id (`host principal
    create --id`, the operator's only, once), and that opener reads and writes the imported stream through HTTP."""
    from test_client import free_port
    import urllib.request
    old, new = ("sqlite:///" + str(tmp_path / n).lstrip("/") for n in ("old.db", "new.db"))
    ann = json.loads(run("host", "principal", "create", "--db", old).stdout)
    s = json.loads(local(old, engines, "open", engines["urls"]["tasks"],
                         actor=ann["principal_id"]).stdout)["event"]["stream_id"]
    assert local(old, engines, "call", "task.open", "-f", "stream_id=" + s, "-f", "task_id=" + U("a"),
                 actor=ann["principal_id"]).returncode == 0
    out = str(tmp_path / "streams.export")
    assert run("export", out, "--db", old).returncode == 0
    assert run("import", out, "--db", new).returncode == 0
    p = local(new, engines, "close", s, "--yes", actor=ann["principal_id"])
    assert p.returncode == client.EXIT_UNAUTHORIZED                  # no tokens moved: the store knows no ann yet
    tf = tmp_path / "issued.token"
    p = run("host", "principal", "create", "--db", new, "--id", ann["principal_id"], "--token-file", str(tf))
    assert p.returncode == 0, p.stderr
    assert json.loads(p.stdout) == {"principal_id": ann["principal_id"]}
    issued = tf.read_text().strip()
    assert issued != ann["token"] and issued not in p.stdout + p.stderr
    assert oct(tf.stat().st_mode & 0o777) == "0o600"
    p = run("host", "principal", "create", "--db", new, "--id", ann["principal_id"])
    assert p.returncode == client.EXIT_REFUSED and p.stderr == "provenstream: refused: principal_must_have_no_token\n"
    p = run("host", "principal", "create", "--db", new, "--token-file", str(tf))
    assert p.returncode == 1 and "never overwritten" in p.stderr                    # nothing asked for, nothing lost
    port = free_port()
    e = {k: v for k, v in os.environ.items() if not k.startswith("PROVENSTREAM_")}
    srv = subprocess.Popen([BIN, "serve", "--db", new, "--engines", engines["dir"], "--port", str(port)], env=e,
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    url = "http://127.0.0.1:%d" % port
    try:
        for _ in range(100):
            try:
                urllib.request.urlopen(url + "/healthz", timeout=1)
                break
            except OSError:
                time.sleep(0.1)
        base = {"PROVENSTREAM_BASE_URL": url}
        assert run("head", s, env=base, token=ann["token"]).returncode == client.EXIT_UNAUTHORIZED   # the old token
        assert json.loads(run("head", s, env=base, token=issued).stdout)["length"] == 2
        p = run("call", "task.open", json.dumps({"stream_id": s, "task_id": U("t")}), env=base, token=issued)
        assert p.returncode == 0 and json.loads(p.stdout)["seq"] == 2, p.stderr
        ev = json.loads(run("events", s, env=base, token=issued).stdout)["events"]
        assert [e["event"] for e in ev] == ["stream.opened", "task.opened", "task.opened"]
        assert {e["actor_id"] for e in ev} == {ann["principal_id"]}
    finally:
        srv.terminate()
        srv.wait(10)


def test_files_commands_ignore_the_mode(engines):
    e = os.path.join(engines["dir"], engines["commit"], "_root", "engine")
    p = run("describe", e, env={"PROVENSTREAM_MODE": "nonsense", "PROVENSTREAM_BASE_URL": "http://h"})
    assert p.returncode == 0 and json.loads(p.stdout)["revision"] == engines["commit"]
    assert "remote" in run("help").stdout


def test_local_writes_beside_a_running_host(dsn, engines, host):
    """A local writer and the host on one stream: every write lands, once, in one order, and the chain holds."""
    ann = host["ann"]
    base = {"PROVENSTREAM_BASE_URL": host["url"]}
    s = json.loads(run("open", engines["urls"]["tasks"], env=base, token=ann["token"]).stdout)["event"]["stream_id"]
    results = {"remote": [], "local": []}

    def remote_writer():
        for i in range(15):
            results["remote"].append(run("call", "task.open", json.dumps({"stream_id": s, "task_id": U("r%d" % i)}),
                                         env=base, token=ann["token"]))

    def local_writer():
        for i in range(15):
            results["local"].append(local(dsn, engines, "call", "task.open",
                                          json.dumps({"stream_id": s, "task_id": U("l%d" % i)}),
                                          actor=ann["principal_id"]))
    ts = [threading.Thread(target=remote_writer), threading.Thread(target=local_writer)]
    [t.start() for t in ts]
    [t.join() for t in ts]
    for side, ps in results.items():
        assert all(p.returncode == 0 for p in ps), (side, [p.stderr for p in ps if p.returncode])
    from provenstream.store import open_store
    store = open_store(dsn)
    try:
        stored = store.read_chained(s)
    finally:
        store.close()
    assert [r[0] for r in stored] == list(range(31))
    ids = [wire.loads(r[1])["command"].get("task_id") for r in stored[1:]]
    assert len(set(ids)) == 30
    rows = [chain.Row(seq, wire.loads(r), wire.loads(e), salt, ch) for seq, r, e, salt, ch in stored]
    assert chain.verify(s, rows).ok and all(r.chain is not None for r in rows)
    receipts = {json.loads(p.stdout)["seq"]: json.loads(p.stdout)["chain"] for ps in results.values() for p in ps}
    assert all(receipts[q] == rows[q].chain.hex() for q in receipts)
