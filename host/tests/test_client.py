# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The command line as a client of a host: base-URL precedence, the token's sources, the error classes and their exit
codes, the convenience commands, and verify against the base URL."""
import json, os, socket, subprocess, time, urllib.request

import pytest

from conftest import CONFIG_DIR, ROOT, U

from provenstream import client

BIN = os.path.join(ROOT, "bin", "provenstream")


def free_port():
    s = socket.socket(); s.bind(("127.0.0.1", 0)); port = s.getsockname()[1]; s.close()
    return port


@pytest.fixture
def host(engines, dsn):
    """A running host and two principals: {"url", "ann", "cy", "dead"} (dead: a URL nothing listens on)."""
    def principal():
        out = subprocess.run([BIN, "host", "principal", "create", "--db", dsn], capture_output=True, text=True,
                             check=True).stdout
        return json.loads(out)
    ann, cy = principal(), principal()
    port = free_port()
    srv = subprocess.Popen([BIN, "serve", "--db", dsn, "--engines", engines["dir"], "--port", str(port)],
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    url = "http://127.0.0.1:%d" % port
    for _ in range(100):
        try:
            urllib.request.urlopen(url + "/healthz", timeout=1)
            break
        except OSError:
            time.sleep(0.1)
    yield {"url": url, "ann": ann, "cy": cy, "dead": "http://127.0.0.1:%d" % free_port()}
    srv.terminate()
    srv.wait(10)


def run(*args, env=None, token=None):
    e = {k: v for k, v in os.environ.items() if not k.startswith("PROVENSTREAM_")}
    e["PROVENSTREAM_CONFIG_DIR"] = CONFIG_DIR          # the tests' own, empty: no stored token, no settings
    if token:
        e["PROVENSTREAM_TOKEN"] = token
    e.update(env or {})
    return subprocess.run([BIN] + list(args), capture_output=True, text=True, env=e)


def test_default_base_url(monkeypatch):
    monkeypatch.delenv("PROVENSTREAM_BASE_URL", raising=False)
    assert client.base_url(None) == client.DEFAULT_BASE_URL.rstrip("/")
    monkeypatch.setenv("PROVENSTREAM_BASE_URL", "http://env.example")
    assert client.base_url(None) == "http://env.example"
    assert client.base_url("http://flag.example/") == "http://flag.example"


def test_client_commands(host, engines, tmp_path):
    ann = host["ann"]["token"]
    proof = engines["urls"]["tasks"]
    good = {"PROVENSTREAM_BASE_URL": host["url"]}
    # base URL: the env var, then the flag over the env var
    p = run("open", proof, "--meta", "hello", env=good, token=ann)
    assert p.returncode == 0, p.stderr
    opened = json.loads(p.stdout)
    s = opened["event"]["stream_id"]
    assert opened["seq"] == 0 and len(opened["chain"]) == 64 and ann not in p.stdout + p.stderr
    p = run("--base-url", host["url"], "head", s, env={"PROVENSTREAM_BASE_URL": host["dead"]}, token=ann)
    assert p.returncode == 0 and json.loads(p.stdout)["length"] == 1
    p = run("head", s, "--base-url", host["dead"], env=good, token=ann)
    assert p.returncode == client.EXIT_UNAVAILABLE and "unavailable" in p.stderr
    # the token from a file
    tf = tmp_path / "token"
    tf.write_text(ann + "\n")
    p = run("--token-file", str(tf), "call", "task.open", "-f", "stream_id=" + s, "-f", "task_id=" + U("first"),
            env=good)
    assert p.returncode == 0 and json.loads(p.stdout)["seq"] == 1
    # each error class
    p = run("revisions", env=good)
    assert p.returncode == client.EXIT_UNAUTHORIZED and "no token" in p.stderr
    p = run("revisions", env=good, token="ps_not-a-token")
    assert p.returncode == client.EXIT_UNAUTHORIZED and "unauthorized" in p.stderr
    p = run("call", "task.open", json.dumps({"stream_id": s, "task_id": U("t")}), env=good, token=host["cy"]["token"])
    assert p.returncode == client.EXIT_REFUSED and p.stderr == "provenstream: refused: only_opener_can_open_tasks\n"
    p = run("call", "task.open", json.dumps({"stream_id": "nope"}), env=good, token=ann)
    assert p.returncode == client.EXIT_PARAMS and "invalid params" in p.stderr
    p = run("call", "task.open", "{not json", env=good, token=ann)
    assert p.returncode == client.EXIT_PARAMS
    p = run("revisions", env={"PROVENSTREAM_BASE_URL": host["dead"]}, token=ann)
    assert p.returncode == client.EXIT_UNAVAILABLE
    # the generic call and the conveniences
    p = run("call", "task.open", json.dumps({"stream_id": s, "task_id": U("t"), "meta": "m"}), env=good, token=ann)
    assert p.returncode == 0 and json.loads(p.stdout)["seq"] == 2
    p = run("events", s, "--from", "1", env=good, token=ann)
    assert [e["seq"] for e in json.loads(p.stdout)["events"]] == [1, 2]
    p = run("revisions", env=good, token=ann)
    assert {r["revision"] for r in json.loads(p.stdout)["revisions"]} == {
        engines[k] for k in ("core", "log", "principals", "tasks", "work", "tower")}
    # verify against the base URL, by default
    p = run("verify", "--stream", s, "--engines", engines["dir"], env=good, token=ann)
    assert p.returncode == 0 and "3 rows replay" in p.stdout, p.stdout + p.stderr
    head = json.loads(run("head", s, env=good, token=ann).stdout)["chain"]
    p = run("verify", "--stream", s, "--engines", engines["dir"], "--head", "2:" + head, env=good, token=ann)
    assert p.returncode == 0
    p = run("close", s, "--yes", env=good, token=ann)
    assert p.returncode == 0
    p = run("close", s, "--yes", env=good, token=ann)
    assert p.returncode == client.EXIT_REFUSED and p.stderr == "provenstream: refused: stream_must_be_open\n"


def test_a_missing_field_still_prints_the_result(capsys):
    """-q with a path the result lacks: exit 5, but the result (a stored write's answer) is printed, the message says
    the call succeeded, and it names the keys that were there."""
    import pytest
    from provenstream import client
    res = {"seq": 0, "event": {"stream_id": "s"}, "chain": "c"}
    with pytest.raises(client.ClientError) as x:
        client.show(res, "stream_id")
    assert x.value.exit_code == 5 and "succeeded" in x.value.message and "chain, event, seq" in x.value.message
    assert '"stream_id": "s"' in capsys.readouterr().out
    client.show(res, "event.stream_id")
    assert capsys.readouterr().out == "s\n"


def test_version():
    """--version prints the package's version and exits 0, with no command and no host."""
    from provenstream import __version__
    r = subprocess.run([BIN, "--version"], capture_output=True, text=True)
    assert (r.returncode, r.stdout.strip()) == (0, "provenstream " + __version__)
