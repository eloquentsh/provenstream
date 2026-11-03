# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The command line, end to end: init and check a new layer project; build, install (never replacing), describe;
issue principals; serve over HTTP; replay and verify a stream (from the database, a host, a rows file, and an engine
built from the stream's own revision: a commit and a package). Tokens go through files and the environment, never
argv."""
import json, os, socket, subprocess, sys, time, urllib.request

import pytest

from conftest import HOST, ROOT, U

BIN = os.path.join(ROOT, "bin", "provenstream")


def cli(*args, check=True, env=None):
    e = {k: v for k, v in os.environ.items() if not k.startswith("PROVENSTREAM_")}
    e.update(env or {})
    p = subprocess.run([BIN] + list(args), capture_output=True, text=True, env=e)
    if check and p.returncode != 0:
        raise AssertionError("provenstream %s: %s%s" % (" ".join(args), p.stdout, p.stderr))
    return p


def rpc(url, token, method, params):
    req = urllib.request.Request(url + "/rpc", json.dumps({"jsonrpc": "2.0", "id": 1, "method": method,
                                                           "params": params}).encode(),
                                 {"Content-Type": "application/json", "Authorization": "Bearer " + token})
    with urllib.request.urlopen(req, timeout=30) as f:
        return json.loads(f.read())


def test_init_and_check(tmp_path):
    d = str(tmp_path / "ledger")
    assert "init:" in cli("init", "ledger", "--dir", d).stdout
    out = cli("check", d).stdout
    assert "check: all passed" in out and "ledger-engine self-test: ok" in out
    assert cli("init", "ledger", "--dir", d, check=False).returncode != 0      # never over an existing project


def test_build_install_never_replaces(engines, tmp_path):
    """A build of a package stamps its package; one commit's packages install side by side, each under its revision
    (`<commit>/<package or _root>`), and none is ever replaced."""
    out = str(tmp_path / "b")
    cli("build", "--repo", engines["repo"], "--commit", engines["commit"], "--out", out, "--reuse-lake", ROOT,
        "--repo-url", engines["url"], "--package", "examples/log")
    prov = json.load(open(os.path.join(out, "PROVENANCE.json")))
    assert prov["revision"] == engines["log"] == engines["commit"] + "/examples/log"
    assert prov["commit"] == engines["commit"] and prov["package"] == "examples/log"
    assert prov["proof_url"] == engines["url"] + "/tree/" + engines["commit"] + "/examples/log"
    assert prov["source"]["tree"] and len(prov["engine"]["sha256"]) == 64
    assert prov["toolchain"]["name"] == "leanprover/lean4:v4.35.0" and prov["schema"]["commands"]
    # rebuilt from the same commit on the same machine: the same bytes
    first = json.load(open(os.path.join(engines["builds"]["log"], "PROVENANCE.json")))
    assert first["engine"]["sha256"] == prov["engine"]["sha256"]
    edir = str(tmp_path / "engines")
    cli("install", engines["builds"]["core"], "--engines", edir)
    cli("install", out, "--engines", edir)
    p = cli("install", out, "--engines", edir, check=False)
    assert p.returncode != 0 and "never replaced" in p.stderr
    m = json.load(open(os.path.join(edir, "revisions.json")))["engines"]
    assert m == {engines["core"]: engines["commit"] + "/_root/engine",
                 engines["log"]: engines["commit"] + "/examples/log/engine"}
    d = json.loads(cli("describe", os.path.join(edir, engines["commit"], "examples", "log", "engine")).stdout)
    assert d["revision"] == engines["commit"] and d["package"] == "examples/log"
    d = json.loads(cli("describe", engines["commit"][:9] + "/examples/log", "--engines", edir).stdout)
    assert d["package"] == "examples/log"
    d = json.loads(cli("describe", engines["commit"][:9], "--engines", edir).stdout)
    assert d["package"] == ""


def free_port():
    s = socket.socket(); s.bind(("127.0.0.1", 0)); port = s.getsockname()[1]; s.close()
    return port


def test_serve_replay_verify(engines, dsn, tmp_path):
    ann = json.loads(cli("host", "principal", "create", "--db", dsn).stdout)
    cy = json.loads(cli("host", "principal", "create", "--db", dsn).stdout)
    tf = tmp_path / "ann.token"
    tf.write_text(ann["token"])
    port = free_port()
    srv = subprocess.Popen([BIN, "serve", "--db", dsn, "--engines", engines["dir"], "--port", str(port)],
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    url = "http://127.0.0.1:%d" % port
    try:
        for _ in range(100):
            try:
                urllib.request.urlopen(url + "/healthz", timeout=1)
                break
            except OSError:
                time.sleep(0.1)
        s = rpc(url, ann["token"], "stream.open",
                {"proof_revision_url": engines["urls"]["tasks"]})["result"]["event"]["stream_id"]
        assert rpc(url, ann["token"], "task.open", {"stream_id": s, "task_id": U("v")})["result"]["seq"] == 1
        assert rpc(url, ann["token"], "task.open", {"stream_id": s, "task_id": U("w")})["result"]["seq"] == 2
        assert rpc(url, cy["token"], "task.open", {"stream_id": s, "task_id": U("w2")})["error"]["data"]["reason"] == \
            "only_opener_can_open_tasks"
        # verify through the host's rows, with an engine built from the stream's own revision (its package)
        out = cli("verify", "--url", url, "--token-file", str(tf), "--stream", s, "--repo", engines["repo"],
                  "--reuse-lake", ROOT).stdout
        assert "3 rows replay through the engine of revision " + engines["tasks"] in out
        p = cli("verify", "--url", url, "--token-file", str(tf), "--stream", s, "--repo", engines["repo"],
                "--package", "examples/log", check=False)
        assert p.returncode == 1 and "the stream names package examples/tasks" in p.stderr
    finally:
        srv.terminate()
        srv.wait(10)
    assert "does not replay: none" in cli("replay", "--db", dsn, "--engines", engines["dir"]).stdout
    assert "3 rows replay" in cli("verify", "--db", dsn, "--stream", s, "--engines", engines["dir"]).stdout
    # a rows file, and a forged row in it
    import psycopg
    with psycopg.connect(dsn) as c:
        rows = [{"stream_id": s, "seq": seq, "request": json.loads(r), "event": json.loads(e)}
                for seq, r, e in c.execute("SELECT seq, request, event FROM events ORDER BY seq")]
    good, bad = str(tmp_path / "rows.jsonl"), str(tmp_path / "forged.jsonl")
    open(good, "w").write("".join(json.dumps(r) + "\n" for r in rows))
    rows[2]["event"]["task_id"] = U("forged")
    open(bad, "w").write("".join(json.dumps(r) + "\n" for r in rows))
    from provenstream.revisions import engine_dir
    tasks_engine = os.path.join(engines["dir"], engine_dir(engines["tasks"]), "engine")
    assert "3 rows replay" in cli("verify", "--rows", good, "--engine", tasks_engine).stdout
    p = cli("verify", "--rows", bad, "--engine", tasks_engine, check=False)
    assert p.returncode == 1 and "DOES NOT REPLAY" in p.stdout
    core_engine = os.path.join(engines["dir"], engine_dir(engines["core"]), "engine")
    p = cli("verify", "--rows", good, "--engine", core_engine, check=False)
    assert p.returncode == 1 and "reports revision" in p.stderr      # another revision's engine is never used
