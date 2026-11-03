# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The command line and a stream's proof: `-h` (the core's two commands, and where the rest come from), `-h --proof`
(a proof's description as Markdown, from an engine, a build directory, a revision URL or a short revision), no
description to be had (exit 6), the check before sending (method_not_found and invalid_params, exit 5, nothing sent),
the description cache, the actor_id the command line fills in and the one the host refuses, and `principal create`,
which never prints a token. Tokens go through files, stdin and the environment, never argv."""
import json, os, re, subprocess

import pytest

from conftest import CONFIG_DIR, ROOT, U
from test_auth import ps, sqlite_host  # noqa: F401  (the running-host fixture)
from test_client import BIN

from provenstream import client
from provenstream.revisions import engine_dir


def env_of(tmp_path, **more):
    e = {k: v for k, v in os.environ.items() if not k.startswith("PROVENSTREAM_")}
    e.update(PROVENSTREAM_CONFIG_DIR=str(tmp_path / "cfg"), HOME=str(tmp_path / "home"))
    e.update(more)
    return e


def cli(tmp_path, *args, **more):
    return subprocess.run([BIN] + list(args), capture_output=True, text=True, env=env_of(tmp_path, **more),
                          cwd=str(tmp_path))


def engine(engines, proof):
    return os.path.join(engines["dir"], engine_dir(engines[proof]), "engine")


def test_help_is_the_readme_s(tmp_path):
    """`provenstream -h`: the core's two commands with the close rule, the rest briefly, the exit codes, and where a
    stream's other commands come from; the README's sample, line for line. No principal.* proof command in it."""
    p = cli(tmp_path, "-h")
    assert p.returncode == 0 and p.stderr == ""
    out = p.stdout
    assert "stream open [PROOF_URL]" in out and "stream close STREAM (--yes | --confirm STREAM)" in out
    assert "only_opener_can_close" in out
    assert out.rstrip().endswith("A stream's other commands come from its proof: provenstream -h --proof <proof> "
                                 "shows them.")
    assert not re.search(r"principal\.[a-z]", out) and "admin" not in out and "agent" not in out
    readme = open(os.path.join(ROOT, "README.md"), encoding="utf-8").read()
    sample = readme.split("$ provenstream -h\n", 1)[1].split("```", 1)[0]
    assert out == sample
    assert cli(tmp_path, "--base-url", "http://127.0.0.1:9", "--help").stdout == out     # global options around it
    sub = cli(tmp_path, "stream", "close", "-h")                                         # a command's own -h
    assert sub.returncode == 0 and "usage: provenstream stream close" in sub.stdout and "--dry-run" in sub.stdout


def test_help_of_the_principals_proof(engines, tmp_path):
    """`-h --proof` on the principals layer's engine: five commands, each with who sends it, its params, its event and
    fields, how to call it and its rules; the answers and the rules tables. The same bytes every time, and from its
    build directory, its full revision URL and its short revision (both through a host)."""
    p = cli(tmp_path, "-h", "--proof", engine(engines, "principals"))
    assert p.returncode == 0, p.stderr
    md = p.stdout
    c = engines["commit"]
    assert md.startswith("# Proof %s/examples/principals\n" % c[:7])
    assert "- commit: %s\n- package: examples/principals\n" % c in md
    assert "- revision URL: %s\n" % engines["urls"]["principals"] in md and "- protocol: 2\n" in md
    assert "- commands: stream.open, stream.close, principal.invite, principal.promote, principal.summon\n" in md
    assert re.findall(r"^## (\S+)$", md, re.M) == ["stream.open", "stream.close", "principal.invite",
                                                   "principal.promote", "principal.summon", "Answers", "Rules"]
    for verb, past in (("invite", "invited"), ("promote", "promoted"), ("summon", "summoned")):
        section = md.split("## principal.%s\n" % verb, 1)[1].split("\n## ", 1)[0]
        assert "Who may send it: an admin" in section
        assert "| stream_id | uuid | required | |" in section and "| principal_id | uuid | required | |" in section
        assert "| meta | meta | optional |" in section
        assert "Event `principal.%s`: `{event, stream_id, actor_id, meta, principal_id}`" % past in section
        assert "provenstream api principal.%s -f stream_id=<stream> -f principal_id=<principal>" % verb in section
        assert "Rules, in order: stream_must_exist, stream_must_be_open, only_admins_can_%s" % verb in section
    assert "actor_id_must_match_the_token" in md and "idempotency_key" in md
    assert "| method_not_found | 5 |" in md and "| refused | 4 |" in md and "| accepted | 0 |" in md
    assert "| stream_must_exist | every command but stream.open |" in md
    assert "| principal_must_be_new | principal.invite, principal.summon |" in md
    assert cli(tmp_path, "-h", "--proof", engine(engines, "principals")).stdout == md     # deterministic
    assert cli(tmp_path, "-h", "--proof", engines["builds"]["principals"]).stdout == md   # a build directory
    db = "sqlite:///" + str(tmp_path / "x.db").lstrip("/")
    for proof in (engines["urls"]["principals"], c[:7] + "/examples/principals"):          # through a host
        p = cli(tmp_path, "-h", "--proof", proof, "--db", db, "--engines", engines["dir"])
        assert p.returncode == 0 and p.stdout == md, (proof, p.stderr)
    # the core's: its two commands
    core = cli(tmp_path, "-h", "--proof", engine(engines, "core")).stdout
    assert "- commands: stream.open, stream.close\n" in core and "- package: (the root)" in core
    # the tasks layer's task.open: parent_task_id an optional uuid (the parent's own task_id), judged last
    tasks = cli(tmp_path, "-h", "--proof", engine(engines, "tasks")).stdout
    section = tasks.split("## task.open\n", 1)[1].split("\n## ", 1)[0]
    assert "| parent_task_id | uuid | optional | or null |" in section, section
    assert "provenstream api task.open -f stream_id=<stream> -f task_id=<task>\n" in section
    assert "Event `task.opened`: `{event, stream_id, actor_id, meta, task_id, parent_task_id}`" in section
    assert "Rules, in order: stream_must_exist, stream_must_be_open, only_opener_can_open_tasks, task_id_must_be_new,\n" \
        "parent_task_must_exist" in section, section


def test_no_description_to_be_had(engines, tmp_path):
    """A proof that names nothing, a path that is no engine, or a host that cannot be reached: a clear error, exit 6,
    and nothing compiled."""
    for proof in ("/nonexistent/engine", "not-a-proof", str(tmp_path)):
        p = cli(tmp_path, "-h", "--proof", proof)
        assert p.returncode == client.EXIT_UNAVAILABLE and "unavailable" in p.stderr and p.stdout == "", (proof, p.stderr)
    # no login, no token, no host named: nothing to ask, and nothing asked (no host is contacted)
    for proof in ("deadbeef1", "deadbeef1/examples/tasks", engines["urls"]["tasks"]):
        p = cli(tmp_path, "-h", "--proof", proof)
        assert p.returncode == client.EXIT_UNAVAILABLE and p.stdout == "", p.stderr
        assert "no description of proof %s could be had: it is not cached under " % proof in p.stderr
        assert "not a path to an engine or a build directory, and the host could not be asked: unauthorized" \
            in p.stderr, p.stderr
    (tmp_path / "t").write_text("ps_nothing\n")
    p = cli(tmp_path, "-h", "--proof", engines["commit"][:9], "--base-url", "http://127.0.0.1:9", "--token-file",
            str(tmp_path / "t"))
    assert p.returncode == client.EXIT_UNAVAILABLE and "no description of proof" in p.stderr, p.stderr
    p = cli(tmp_path, "-h", "--proof", engines["urls"]["tasks"], "--base-url", "http://127.0.0.1:9", "--token-file",
            str(tmp_path / "t"))
    assert p.returncode == client.EXIT_UNAVAILABLE
    # the check before sending, with no description to be had: the same, and nothing sent
    p = cli(tmp_path, "api", "log.append", "-f", "stream_id=" + U("s"), "-f", "text=x", "--base-url",
            "http://127.0.0.1:9", "--token-file", str(tmp_path / "t"))
    assert p.returncode == client.EXIT_UNAVAILABLE and "no description of stream %s's revision could be had" % U("s") \
        in p.stderr and "the host could not be asked: unavailable: cannot reach" in p.stderr, p.stderr


@pytest.fixture
def local(engines, tmp_path):
    """A local-mode session on a fresh SQLite file: the operator's first principal (its token to a file), a second
    created by it, and a core stream the first opened."""
    db = "sqlite:///" + str(tmp_path / "demo.db").lstrip("/")
    run = lambda *args: cli(tmp_path, *(list(args) + ["--db", db]), PROVENSTREAM_ENGINES=engines["dir"])
    p = run("host", "principal", "create", "--token-file", str(tmp_path / "me.token"), "-q", "principal_id")
    assert p.returncode == 0, p.stderr
    me = p.stdout.strip()
    p = run("principal", "create", "--as", me, "--token-file", str(tmp_path / "other.token"))
    assert p.returncode == 0, p.stderr
    other = p.stdout.strip()
    for name in ("me", "other"):
        tok = (tmp_path / (name + ".token")).read_text().strip()
        assert tok and oct((tmp_path / (name + ".token")).stat().st_mode & 0o777) == "0o600"
        assert tok not in p.stdout + p.stderr
    p = run("stream", "open", engines["urls"]["core"], "--as", me, "-q", "event.stream_id")
    assert p.returncode == 0, p.stderr
    return {"run": run, "db": db, "me": me, "other": other, "s": p.stdout.strip()}


def received(h):
    from provenstream.host import Host, Operator
    host = Host.open(h["db"])
    try:
        rows = host.query("usage.get", auth=Operator(None), scope="stream", key=h["s"])["usage"]
    finally:
        host.close()
    return rows[0]["received"] if rows else 0


def test_the_check_before_sending(local, engines, tmp_path):
    """A command its stream's proof does not describe, or params it does not take, are answered by the command line
    itself from the description (cached under ~/.provenstream/proofs), exit 5, and nothing is sent."""
    run, s, me = local["run"], local["s"], local["me"]
    before = received(local)
    p = run("api", "stream.panic", "-f", "stream_id=" + s, "--as", me)
    assert p.returncode == client.EXIT_PARAMS and p.stderr == (
        "provenstream: method not found: stream.panic is not a command of %s (its description; nothing sent)\n"
        % engines["commit"][:7])
    p = run("api", "task.open", "-f", "stream_id=" + s, "-f", "task_id=" + U("t"), "--as", me)
    assert p.returncode == client.EXIT_PARAMS and "task.open is not a command of" in p.stderr
    for bad in (["-f", "meta=5"], ["-f", "x=1"], ["-f", "actor_id=me"], ["-f", "idempotency_key="]):
        p = run("api", "stream.close", "-f", "stream_id=" + s, *bad, "--as", me)
        assert p.returncode == client.EXIT_PARAMS and "nothing sent" in p.stderr and "invalid params" in p.stderr, bad
    p = run("api", "task.open", "-f", "task_id=" + U("t"), "--as", me)                    # no stream: no proof to ask
    assert p.returncode == client.EXIT_PARAMS and "stream_id: required" in p.stderr
    assert received(local) == before                                                   # the host received none of them
    cached = tmp_path / "cfg" / "proofs" / engines["commit"] / "_root" / "description.json"
    assert json.loads(cached.read_text())["revision"] == engines["commit"]
    # with --proof, the check needs no host at all: one that cannot be reached is never asked
    (tmp_path / "t").write_text("ps_nothing\n")
    p = cli(tmp_path, "api", "stream.panic", "-f", "stream_id=" + s, "--proof", engine(engines, "core"),
            "--base-url", "http://127.0.0.1:9", "--token-file", str(tmp_path / "t"))
    assert p.returncode == client.EXIT_PARAMS and "nothing sent" in p.stderr, p.stderr
    # --proof checks against another proof's description: the tasks layer's task.open passes the check, and the
    # stream's own proof (the core's) refuses it at the host, method_not_found
    p = run("api", "task.open", "-f", "stream_id=" + s, "-f", "task_id=" + U("t"), "--as", me, "--proof",
            engine(engines, "tasks"))
    assert p.returncode == client.EXIT_PARAMS and "method not found" in p.stderr and "nothing sent" not in p.stderr
    # parent_task_id is an optional uuid: a seq or a non-uuid text is refused before sending
    for bad in ("parent_task_id=3", "parent_task_id=t1", "parent_task_id=" + U("t").upper()):
        p = run("api", "task.open", "-f", "stream_id=" + s, "-f", "task_id=" + U("t"), "-f", bad, "--as", me,
                "--proof", engine(engines, "tasks"))
        assert p.returncode == client.EXIT_PARAMS and "parent_task_id: expected a canonical lowercase UUID or null" \
            in p.stderr and "nothing sent" in p.stderr, (bad, p.stderr)
    assert received(local) == before


def test_actor_id(local, tmp_path):
    """The command line fills in actor_id from --as; one naming another principal is refused by the host, exit 4."""
    run, s, me, other = local["run"], local["s"], local["me"], local["other"]
    p = run("api", "stream.close", "-f", "stream_id=" + s, "-f", "actor_id=" + me, "--as", other)
    assert p.returncode == client.EXIT_REFUSED and p.stderr == "provenstream: refused: actor_id_must_match_the_token\n"
    p = run("stream", "close", s, "--yes", "--as", other)
    assert p.returncode == client.EXIT_REFUSED and p.stderr == "provenstream: refused: only_opener_can_close\n"
    p = run("stream", "close", s, "--yes", "--as", me, "-q", "event.actor_id")
    assert p.returncode == 0 and p.stdout.strip() == me


def test_principal_create_never_prints_a_token(sqlite_host, engines, tmp_path):
    """Remote, as a signed-in principal: only the new principal_id is printed; its token goes to --token-file (0600,
    never over a file) or is stored for the host under --save-as NAME, and --principal NAME sends it. The actor_id of
    a token from PROVENSTREAM_TOKEN or --token-file is the host's whoami."""
    h = sqlite_host
    assert ps(h["cfg"], "login", "--base-url", h["url"], "--default", stdin=h["ann"]["token"]).returncode == 0
    p = ps(h["cfg"], "principal", "create", "--save-as", "agent")
    assert p.returncode == 0, p.stderr
    agent = p.stdout.strip()
    assert re.fullmatch(r"[0-9a-f-]{36}", agent) and agent != h["ann"]["principal_id"]
    creds = json.loads((h["cfg"] / "credentials.json").read_text())[h["url"]]
    assert creds["active"] == h["ann"]["principal_id"] and creds["principals"][agent]["name"] == "agent"
    stored = creds["principals"][agent]["token"]
    assert stored not in p.stdout + p.stderr
    p = ps(h["cfg"], "api", "whoami", "--principal", "agent")
    assert p.returncode == 0 and json.loads(p.stdout) == {"principal_id": agent}
    tf = tmp_path / "new.token"
    p = ps(h["cfg"], "principal", "create", "--token-file", str(tf), "-q", "principal_id")
    assert p.returncode == 0 and tf.read_text().strip() not in p.stdout + p.stderr
    assert oct(tf.stat().st_mode & 0o777) == "0o600"
    newest = p.stdout.strip()
    p = ps(h["cfg"], "principal", "create", "--token-file", str(tf))
    assert p.returncode == 1 and "never overwritten" in p.stderr
    p = ps(h["cfg"], "principal", "create")
    assert p.returncode == 2 and "never printed" in p.stderr
    s = json.loads(ps(h["cfg"], "stream", "open", engines["urls"]["log"], "--no-use").stdout)["event"]["stream_id"]
    p = ps(h["cfg"], "api", "log.append", "-f", "stream_id=" + s, "-f", "text=hi", "--principal", "agent")
    assert p.returncode == client.EXIT_REFUSED and "only_opener_can_append" in p.stderr
    p = ps(h["cfg"], "api", "log.append", "-f", "stream_id=" + s, "-f", "text=hi",
           env={"PROVENSTREAM_TOKEN": h["ann"]["token"]})
    assert p.returncode == 0 and json.loads(p.stdout)["event"]["actor_id"] == h["ann"]["principal_id"]
    p = ps(h["cfg"], "--token-file", str(tf), "api", "log.append", "-f", "stream_id=" + s, "-f", "text=x", "-f",
           "actor_id=" + h["ann"]["principal_id"])
    assert p.returncode == client.EXIT_REFUSED and "actor_id_must_match_the_token" in p.stderr
    p = ps(h["cfg"], "--token-file", str(tf), "stream", "close", s, "--dry-run", "-q", "caller_id")
    assert p.stdout.strip() == newest
