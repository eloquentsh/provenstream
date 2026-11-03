# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The command tree and the flat aliases giving the same answers; the current stream from a flag, the environment, a
project file (found walking up) and the user config; aliases, suffixes (prefixes refused) and revision prefixes; a
proof URL from git; close's confirmation (no terminal, --yes, --confirm, --dry-run, and a real terminal through a
pty); and -q. Against a real `serve` on a temporary SQLite store, logged in as in round one; every command runs with
a config directory of the test's own, in a working directory of its own."""
import io, json, os, pty, select, subprocess, sys

import pytest

from conftest import U, _git
from test_auth import sqlite_host  # noqa: F401  (the running-host fixture)
from test_client import BIN

from provenstream import cli_stream, client, config, context
from provenstream.client import ClientError


def ps(cfg, *args, cwd, env=None, stdin=None):
    e = {k: v for k, v in os.environ.items() if not k.startswith("PROVENSTREAM_")}
    e["PROVENSTREAM_CONFIG_DIR"] = str(cfg)
    e.update(env or {})
    return subprocess.run([BIN] + list(args), capture_output=True, text=True, env=e, input=stdin or "",
                          cwd=str(cwd))


@pytest.fixture
def h(sqlite_host, engines, tmp_path):
    """The host, ann logged in to it as the default host, a working directory `w`, and `ps(*args, cwd=w)`."""
    h = dict(sqlite_host)
    h["w"] = tmp_path / "w"
    h["w"].mkdir()
    h["proof"] = engines["urls"]["tasks"]
    h["run"] = lambda *args, cwd=None, env=None, stdin=None: ps(h["cfg"], *args, cwd=cwd or h["w"], env=env,
                                                                stdin=stdin)
    p = h["run"]("login", "--base-url", h["url"], "--default", stdin=h["ann"]["token"])
    assert p.returncode == 0, p.stderr
    return h


def opened(h, *args, cwd=None):
    p = h["run"]("stream", "open", h["proof"], *args, cwd=cwd)
    assert p.returncode == 0, p.stderr
    return json.loads(p.stdout)["event"]["stream_id"]


def length(h, s):
    return json.loads(h["run"]("head", s).stdout)["length"]


# -- the tree and its flat aliases ----------------------------------------------------------------------------------

def test_tree_and_flat_aliases_agree(h, engines):
    r = h["run"]
    s = opened(h, "--no-use")
    for flat, tree in ((["head", s], ["stream", "head", s]),
                       (["events", s, "--from", "0"], ["stream", "events", s, "--from", "0"]),
                       (["revisions"], ["revision", "list"]),
                       (["call", "whoami"], ["api", "whoami"]),
                       (["call", "stream.head", json.dumps({"stream_id": s})],
                        ["api", "stream.head", "-f", "stream_id=" + s]),
                       (["mode", "--json"], ["status", "--json"]),
                       (["describe", os.path.join(engines["dir"], engines["commit"], "_root", "engine")],
                        ["engine", "describe", os.path.join(engines["dir"], engines["commit"], "_root", "engine")])):
        a, b = r(*flat), r(*tree)
        assert a.returncode == b.returncode == 0, (flat, a.stderr, b.stderr)
        assert a.stdout == b.stdout, flat
    a = json.loads(r("call", "task.open", "-f", "stream_id=" + s, "-f", "task_id=" + U("a")).stdout)
    b = json.loads(r("api", "task.open", json.dumps({"stream_id": s, "task_id": U("b")})).stdout)
    assert (a["seq"], b["seq"]) == (1, 2) and a["event"]["event"] == b["event"]["event"] == "task.opened"
    assert a["event"]["actor_id"] == b["event"]["actor_id"] == h["ann"]["principal_id"]     # filled in by the CLI
    for gone in (["agent", s, h["cy"]["principal_id"]], ["admin", s, h["cy"]["principal_id"]],
                 ["stream", "agent", "add", h["cy"]["principal_id"]], ["stream", "admin", "add", U("x")]):
        assert r(*gone).returncode == 2, gone                                             # removed: usage
    p = r("help")
    assert "principal create" in p.stdout and "revisions" in p.stdout and "admin" not in p.stdout
    # api -f: JSON when it parses, merged over the JSON params
    ev = json.loads(r("api", "stream.events", json.dumps({"stream_id": s}), "-f", "from=1").stdout)["events"]
    assert [e["seq"] for e in ev] == [1, 2]
    p = r("api", "stream.head", "-f", "nonsense")
    assert p.returncode == client.EXIT_PARAMS and "key=value" in p.stderr


# -- the current stream ---------------------------------------------------------------------------------------------

def test_current_stream_precedence_and_the_walk_up(h):
    r = h["run"]
    a, b, c = (opened(h, "--no-use") for _ in range(3))
    p = r("stream", "head")
    assert p.returncode == client.EXIT_PARAMS and "stream use" in p.stderr           # none yet
    assert r("stream", "use", a).returncode == 0                                       # no project: the user config
    assert json.loads((h["cfg"] / "config.json").read_text())["stream"] == a
    proj = h["w"] / "proj"
    deep = proj / "sub" / "deeper"
    deep.mkdir(parents=True)
    p = r("stream", "use", b, "--project", cwd=proj)
    assert p.returncode == 0 and str(proj / ".provenstream" / "client.json") in p.stdout, p.stderr
    pf = proj / ".provenstream" / "client.json"
    assert json.loads(pf.read_text()) == {"stream": b} and oct(pf.stat().st_mode & 0o777) == "0o644"
    head = lambda *args, cwd, env=None: json.loads(r("stream", "head", *args, cwd=cwd, env=env).stdout)["stream_id"]
    assert head(cwd=h["w"]) == a                                                       # outside: the user config
    assert head(cwd=deep) == b                                                         # walking up: the project's
    assert head(cwd=deep, env={"PROVENSTREAM_STREAM": c}) == c                         # env over the project file
    assert head(a, cwd=deep, env={"PROVENSTREAM_STREAM": c}) == a                      # the argument over all
    # the other commands that default to it
    ev = json.loads(r("events", cwd=deep).stdout)
    assert ev["stream_id"] == b
    # inside the project, use writes the project file; --view says where it came from; --unset forgets it
    assert r("stream", "use", c, cwd=deep).returncode == 0
    assert json.loads(pf.read_text())["stream"] == c
    assert json.loads((h["cfg"] / "config.json").read_text())["stream"] == a
    v = json.loads(r("stream", "use", "--view", cwd=deep).stdout)
    assert v["stream"] == c and v["from"].startswith("project") and v["project"] == str(pf)
    assert r("stream", "use", "--view", "-q", "from", cwd=h["w"]).stdout.startswith("config")
    assert r("stream", "use", "--unset", cwd=deep).returncode == 0 and "stream" not in json.loads(pf.read_text())
    p = r("stream", "head", cwd=deep)
    assert p.returncode == 0 and json.loads(p.stdout)["stream_id"] == a                # the user config again
    # config list shows the project's value and where it came from
    pf.write_text(json.dumps({"stream": b}))
    p = r("config", "list", cwd=deep)
    assert b in p.stdout and "project (%s)" % pf in p.stdout


def test_find_project_stops_at_homes_parent(tmp_path):
    home = tmp_path / "home"
    (tmp_path / ".provenstream").mkdir()
    (tmp_path / ".provenstream" / "client.json").write_text("{}")          # above $HOME: never read
    deep = home / "a" / "b"
    deep.mkdir(parents=True)
    env = {"HOME": str(home), "PROVENSTREAM_CONFIG_DIR": str(tmp_path / "cfg")}
    assert context.find_project(str(deep), env) is None
    (home / ".provenstream").mkdir()
    (home / ".provenstream" / "client.json").write_text("{}")              # $HOME's own: the user config directory
    assert context.find_project(str(deep), env) is None
    (home / "a" / ".provenstream").mkdir()
    (home / "a" / ".provenstream" / "client.json").write_text("{}")
    assert context.find_project(str(deep), env) == str(home / "a" / ".provenstream" / "client.json")
    (home / "a" / ".provenstream" / "client.json").write_text(json.dumps({"token": "x"}))
    with pytest.raises(ClientError) as x:
        context.load_project(env, str(deep))
    assert x.value.exit_code == client.EXIT_PARAMS and "unknown keys token" in x.value.message


def test_project_host_is_a_default_and_never_selects_the_mode(h, tmp_path):
    import site
    r = h["run"]
    proj = h["w"] / "p"
    (proj / ".provenstream").mkdir(parents=True)
    (proj / ".provenstream" / "client.json").write_text(json.dumps({"host": h["url"]}))
    assert r("config", "unset", "default_host").returncode == 0
    d = json.loads(r("mode", "--json", cwd=proj).stdout)
    assert d["target"] == h["url"] and d["host_from"].startswith("project host") and \
        d["principal"]["principal_id"] == h["ann"]["principal_id"]
    d = json.loads(r("mode", "--json", cwd=proj, env={"PROVENSTREAM_BASE_URL": "http://127.0.0.1:9"}).stdout)
    assert d["target"] == "http://127.0.0.1:9" and d["host_from"] == "PROVENSTREAM_BASE_URL"
    assert "project (%s)" % (proj / ".provenstream" / "client.json") in r("config", "list", cwd=proj).stdout
    home = {"HOME": str(tmp_path), "PYTHONUSERBASE": site.getuserbase()}
    p = r("host", "principal", "create", cwd=proj, env=home)        # local only: still the default database
    assert p.returncode == 0, p.stderr
    assert (tmp_path / ".provenstream" / "streams.db").exists()


# -- aliases, suffixes, revision prefixes ---------------------------------------------------------------------------

S1 = "01890000-0000-7000-8000-00001234abcd"
S2 = "01890000-0001-7000-8000-99991234abcd"


def test_resolution_rules(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    env = {"PROVENSTREAM_CONFIG_DIR": str(tmp_path / "cfg"), "HOME": str(tmp_path)}
    res = lambda arg: context.resolve_stream(arg, env)
    assert res(S1.upper()) == S1 and res(S1.replace("-", "")) == S1               # a full id: as it is
    with pytest.raises(ClientError) as x:
        res("1234abcd")
    assert x.value.exit_code == client.EXIT_PARAMS and "no stream known here" in x.value.message
    context.remember(S1, env)
    context.remember(S2, env)
    assert context.recent(env) == [S2, S1]
    with pytest.raises(ClientError) as x:
        res("1234abcd")                                                          # both end so: ambiguous
    assert x.value.exit_code == client.EXIT_PARAMS and S1 in x.value.message and S2 in x.value.message
    assert res("01234abcd") == S1 and res("8000-99991234abcd") == S2 and res("91234ABCD") == S2
    for prefix in ("01890000", "018900000000"):
        with pytest.raises(ClientError) as x:
            res(prefix)                                                          # UUIDv7: a prefix is a timestamp
        assert "prefix" in x.value.message and "last digits" in x.value.message
    with pytest.raises(ClientError) as x:
        res("234abcd")
    assert "8 or more" in x.value.message
    # aliases: the project's shadow the user's
    config.set_value("aliases.ledger", S1, env)
    assert res("ledger") == S1
    (tmp_path / ".provenstream").mkdir()
    (tmp_path / ".provenstream" / "client.json").write_text(json.dumps({"aliases": {"ledger": S2}}))
    env["HOME"] = "/nonexistent/home"                                         # tmp_path is no longer $HOME
    assert res("ledger") == S2 and context.alias_of(S2, env) == "ledger"
    with pytest.raises(ClientError) as x:
        res("nope")
    assert "not a UUID, an alias" in x.value.message and "ledger" in x.value.message
    # on a terminal, a stream not given as a full id is named on stderr
    class Tty(io.StringIO):
        def isatty(self):
            return True
    err = Tty()
    monkeypatch.setattr(sys, "stderr", err)
    assert context.stream_or_current("ledger", "head", env) == S2 and context.stream_or_current(S1, "head", env) == S1
    assert err.getvalue() == "stream: ledger (%s)\n" % S2
    monkeypatch.undo()
    monkeypatch.chdir(tmp_path)
    for bad in ("deadbeef", "1x", "-a", ""):
        with pytest.raises(ClientError):
            context.check_alias(bad)
    # the recent list keeps the last 50
    for i in range(60):
        context.remember(U("r%d" % i), env)
    assert len(context.recent(env)) == 50 and context.recent(env)[0] == U("r59")
    # revisions: a unique prefix of 7 or more, and a package (bare hex is the root package)
    revs = ["a" * 40, "ab" + "0" * 38, "abc" + "1" * 37, "abc" + "1" * 37 + "/examples/tasks"]
    assert context.resolve_revision("abc1111", revs) == revs[2]
    assert context.resolve_revision("abc1111/examples/tasks", revs) == revs[3]
    for bad, why in (("abc111", "7 or more"), ("ab11111", "no revision"), ("aaaaaaa", None),
                     ("abc1111/examples/log", "no revision"), ("abc1111/", "7 or more"),
                     ("abc1111/../x", "7 or more")):
        if why is None:
            assert context.resolve_revision(bad, revs) == revs[0]
            continue
        with pytest.raises(ClientError) as x:
            context.resolve_revision(bad, revs)
        assert why in x.value.message
    with pytest.raises(ClientError) as x:
        context.resolve_revision("abcd", revs + ["abcd" + "2" * 36, "abcd" + "3" * 36])
    assert "7 or more" in x.value.message
    with pytest.raises(ClientError) as x:
        context.resolve_revision("abcd222", revs + ["abcd222" + "2" * 33, "abcd222" + "3" * 33])
    assert "names 2 revisions" in x.value.message


def test_aliases_suffixes_and_revision_prefixes_end_to_end(h, engines):
    r = h["run"]
    s = opened(h, "--alias", "ledger")
    cfg = json.loads((h["cfg"] / "config.json").read_text())
    assert cfg["stream"] == s and cfg["aliases"] == {"ledger": s}
    assert json.loads(r("head", "ledger").stdout)["stream_id"] == s
    assert json.loads(r("stream", "head", s[-10:]).stdout)["stream_id"] == s        # a suffix of a recent stream
    p = r("head", s.replace("-", "")[:12])
    assert p.returncode == client.EXIT_PARAMS and "prefix" in p.stderr
    p = r("head", "nosuchalias")
    assert p.returncode == client.EXIT_PARAMS and "ledger" in p.stderr
    assert r("stream", "alias", "books", "ledger").returncode == 0
    al = json.loads(r("stream", "alias", "--list").stdout)
    assert al == {"books": s, "ledger": s}
    assert r("config", "get", "aliases.books").stdout.strip() == s
    assert "aliases.books" in r("config", "list").stdout
    assert r("stream", "alias", "--remove", "books").returncode == 0
    assert r("stream", "alias", "--remove", "books").returncode == 1
    assert json.loads(r("config", "get", "aliases").stdout) == {"ledger": s}
    for args in (["set", "stream", "not-a-uuid"], ["set", "proof_revision_url", "nope"], ["set", "aliases.9x", s],
                 ["set", "aliases.ok", "nope"]):
        p = r("config", *args)
        assert p.returncode == client.EXIT_PARAMS, (args, p.stderr)
    p = r("stream", "open", h["proof"], "--alias", "deadbeef")
    assert p.returncode == client.EXIT_PARAMS and length(h, s) == 1                # refused before anything opened
    # a revision by 7 hex digits and its package: describe it, open with it, and an engine of the engines directory
    c = engines["commit"]
    d = json.loads(r("revision", "describe", c[:7] + "/examples/tasks").stdout)
    assert (d["revision"], d["package"]) == (c, "examples/tasks")
    assert json.loads(r("revision", "describe", c[:7]).stdout)["package"] == ""
    p = r("stream", "open", c[:7] + "/examples/tasks", "--no-use")
    assert p.returncode == 0 and "proof URL: %s" % engines["urls"]["tasks"] in p.stderr, p.stderr
    assert json.loads(p.stdout)["event"]["proof_revision_url"] == engines["urls"]["tasks"]
    p = r("stream", "open", c[:7], "--no-use")
    assert json.loads(p.stdout)["event"]["proof_revision_url"] == "%s/commit/%s" % (engines["url"], c)
    assert r("config", "get", "stream").stdout.strip() == s                           # --no-use: still the first
    d = json.loads(r("engine", "describe", c[:8] + "/tests/tower", "--engines", engines["dir"]).stdout)
    assert (d["revision"], d["package"]) == (c, "tests/tower")
    p = r("revision", "describe", "0000000")
    assert p.returncode == client.EXIT_PARAMS and engines["core"] in p.stderr


# -- a proof URL from git, and the configured one -------------------------------------------------------------------

def test_https_of():
    f = context.https_of
    assert f("git@example.org:someone/proofs.git") == "https://example.org/someone/proofs"
    assert f("ssh://git@Example.org:2222/someone/proofs.git/") == "https://example.org/someone/proofs"
    assert f("https://user:pw@example.org/someone/proofs.git") == "https://example.org/someone/proofs"
    assert f("http://example.org:8080/a/b") == "https://example.org:8080/a/b"
    assert f("git://example.org/a/b.git") == "https://example.org/a/b"
    assert f("/srv/git/proofs.git") is None and f("file:///srv/git/proofs.git") is None and f("../x") is None


def test_proof_url_from_git(tmp_path):
    bare, repo = str(tmp_path / "origin.git"), str(tmp_path / "repo")
    subprocess.run(["git", "init", "-q", "--bare", bare], check=True)
    subprocess.run(["git", "-c", "init.defaultBranch=main", "init", "-q", repo], check=True)
    with pytest.raises(ClientError) as x:
        context.proof_url_from_git(str(tmp_path))
    assert x.value.exit_code == 1 and "not in a git repository" in x.value.message
    with open(os.path.join(repo, "provenstream.json"), "w") as f:
        f.write("{}\n")
    os.makedirs(os.path.join(repo, "sub"))
    with pytest.raises(ClientError) as x:
        context.proof_url_from_git(repo)
    assert "no commit" in x.value.message
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "first")
    head = subprocess.run(["git", "-C", repo, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    with pytest.raises(ClientError) as x:
        context.proof_url_from_git(repo)
    assert "no remote named origin" in x.value.message
    _git(repo, "remote", "add", "origin", "https://example.org/someone/proofs.git")
    _git(repo, "config", "remote.origin.pushurl", bare)          # fetched from the URL, pushed to the bare repository
    with pytest.raises(ClientError) as x:
        context.proof_url_from_git(os.path.join(repo, "sub"))
    assert "push it first" in x.value.message                    # not pushed: no remote branch holds HEAD
    _git(repo, "push", "-q", "-u", "origin", "main")
    assert context.proof_url_from_git(os.path.join(repo, "sub")) == "https://example.org/someone/proofs/commit/" + head
    with open(os.path.join(repo, "sub", "provenstream.json"), "w") as f:
        f.write("{}\n")                                     # a package below the top: its own revision of HEAD
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "a package")
    _git(repo, "push", "-q", "origin", "main")
    head = subprocess.run(["git", "-C", repo, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    assert context.proof_url_from_git(os.path.join(repo, "sub")) == \
        "https://example.org/someone/proofs/tree/%s/sub" % head
    assert context.proof_url_from_git(repo) == "https://example.org/someone/proofs/commit/" + head
    with open(os.path.join(repo, "provenstream.json"), "w") as f:
        f.write('{"changed": true}\n')
    with pytest.raises(ClientError) as x:
        context.proof_url_from_git(repo)
    assert "uncommitted changes" in x.value.message              # dirty
    _git(repo, "checkout", "--", "provenstream.json")
    with open(os.path.join(repo, "untracked"), "w") as f:
        f.write("x")
    assert context.proof_url_from_git(repo).endswith(head)       # untracked files do not count
    other = str(tmp_path / "plain")
    subprocess.run(["git", "init", "-q", other], check=True)
    with pytest.raises(ClientError) as x:
        context.proof_url_from_git(other)
    assert "no provenstream.json" in x.value.message


def test_open_from_configuration_and_from_git(h):
    r = h["run"]
    p = r("stream", "open")
    assert p.returncode == 1 and "not in a git repository" in p.stderr                # nothing configured, no git
    proj = h["w"] / "proj"
    (proj / ".provenstream").mkdir(parents=True)
    (proj / ".provenstream" / "client.json").write_text(json.dumps({"proof_revision_url": h["proof"]}))
    p = r("stream", "open", "--alias", "ledger", "--meta", "m", cwd=proj)
    assert p.returncode == 0, p.stderr
    s = json.loads(p.stdout)["event"]["stream_id"]
    pf = json.loads((proj / ".provenstream" / "client.json").read_text())
    assert pf == {"proof_revision_url": h["proof"], "stream": s, "aliases": {"ledger": s}}
    assert "stream" not in json.loads((h["cfg"] / "config.json").read_text())       # the project's, not the user's
    assert json.loads(r("stream", "head", cwd=proj).stdout)["stream_id"] == s
    p = r("stream", "open", "--from-git", cwd=proj)
    assert p.returncode == 1 and "not in a git repository" in p.stderr                # --from-git skips the configured
    p = r("stream", "open", h["proof"], "--from-git", cwd=proj)
    assert p.returncode == 2
    assert r("config", "set", "proof_revision_url", h["proof"]).returncode == 0       # outside a project: the config's
    p = r("open")
    assert p.returncode == 0 and json.loads(p.stdout)["event"]["proof_revision_url"] == h["proof"]


# -- close ----------------------------------------------------------------------------------------------------------

def test_close_needs_a_confirmation(h):
    r = h["run"]
    s = opened(h, "--alias", "ledger")
    t = opened(h, "--no-use")
    p = r("stream", "close")
    assert p.returncode == 2                                                         # never the current stream
    for args in ([s], ["ledger"], [s[-8:]]):
        p = r("close", *args)
        assert p.returncode == 2 and "--yes" in p.stderr and "--confirm" in p.stderr, p.stderr
    p = r("stream", "close", s, "--confirm", t)
    assert p.returncode == 1 and "another stream" in p.stderr
    assert length(h, s) == 1
    # a dry run reads, and sends nothing
    d = json.loads(r("stream", "close", "ledger", "--dry-run").stdout)
    assert d == {"stream_id": s, "alias": "ledger", "proof_revision_url": h["proof"],
                 "opener_id": h["ann"]["principal_id"], "caller_id": h["ann"]["principal_id"], "caller_is_opener": True,
                 "closed": False, "would_close": True, "sent": False}
    assert r("stream", "close", s, "--dry-run", "-q", "would_close").stdout.strip() == "true"
    assert r("api", "task.open", "-f", "stream_id=" + s, "-f", "task_id=" + U("t")).returncode == 0
    p = r("stream", "close", s, "--dry-run", env={"PROVENSTREAM_TOKEN": h["cy"]["token"]})
    d = json.loads(p.stdout)
    assert p.returncode == 0 and d["caller_is_opener"] is False and d["would_close"] is False
    assert d["caller_id"] == h["cy"]["principal_id"]                                   # from the host's whoami
    p = r("stream", "close", s, "--yes", env={"PROVENSTREAM_TOKEN": h["cy"]["token"]})
    assert p.returncode == client.EXIT_REFUSED and p.stderr == "provenstream: refused: only_opener_can_close\n"
    from provenstream.store import open_store
    store = open_store(h["db"])
    try:
        assert len(store.read_chained(s)) == 2                                         # the store: nothing appended
    finally:
        store.close()
    p = r("stream", "close", s, "--confirm", "ledger")
    assert p.returncode == 0 and json.loads(p.stdout)["event"]["event"] == "stream.closed"
    d = json.loads(r("stream", "close", s, "--dry-run").stdout)
    assert d["closed"] is True and d["would_close"] is False
    p = r("close", t, "--yes", "-q", "seq")
    assert p.returncode == 0 and p.stdout == "1\n"


def tty_run(h, args, answer):
    """The command on a pseudo-terminal (stdin and stderr), `answer` typed at the prompt: (exit, stdout, terminal)."""
    e = {k: v for k, v in os.environ.items() if not k.startswith("PROVENSTREAM_")}
    e["PROVENSTREAM_CONFIG_DIR"] = str(h["cfg"])
    m, sl = pty.openpty()
    p = subprocess.Popen([BIN] + args, stdin=sl, stderr=sl, stdout=subprocess.PIPE, env=e, cwd=str(h["w"]))
    os.close(sl)
    seen = b""
    try:
        while b"to close it: " not in seen:
            if not select.select([m], [], [], 60)[0]:
                break
            try:
                chunk = os.read(m, 4096)
            except OSError:
                break
            if not chunk:
                break
            seen += chunk
        os.write(m, (answer + "\n").encode())
        out = p.stdout.read().decode()
        p.wait(60)
    finally:
        os.close(m)
    return p.returncode, out, seen.decode(errors="replace")


def test_close_on_a_terminal(h):
    s = opened(h, "--alias", "ledger")
    code, out, seen = tty_run(h, ["stream", "close", "ledger"], "wrong")
    assert code == 1 and out == "" and length(h, s) == 1
    assert "close stream %s" % s in seen and "alias:   ledger" in seen and h["proof"] in seen
    assert "opener:  " + h["ann"]["principal_id"] in seen
    code, out, seen = tty_run(h, ["close", s[-8:]], s[-8:])
    assert code == 0 and json.loads(out)["event"]["event"] == "stream.closed", seen
    assert length(h, s) == 2


def test_the_prompt():
    s, view = S1, {"proof_revision_url": "https://example.org/a/b/commit/" + "a" * 40, "opener_id": U("ann")}
    for answer, ok in (("ledger", True), (S1, True), (S1.upper(), True), (S1[-8:], True), (S1[-8:].upper(), True),
                       ("", False), ("ledge", False), (S1[:8], False), (S2, False)):
        err = io.StringIO()
        assert cli_stream.confirm(s, view, "ledger", io.StringIO(answer + "\n"), err) is ok, answer
        assert "close stream " + S1 in err.getvalue() and U("ann") in err.getvalue()
    assert cli_stream.confirm(s, view, None, io.StringIO(""), io.StringIO()) is False    # end of input


# -- -q -------------------------------------------------------------------------------------------------------------

def test_field_paths(h):
    r = h["run"]
    p = r("stream", "open", h["proof"], "-q", "event.stream_id")
    s = p.stdout.strip()
    assert p.returncode == 0 and context.canonical(s) == s
    assert r("head", "-q", "length").stdout == "1\n"
    assert r("events", "-q", "events.0.seq").stdout == "0\n"
    assert r("events", "-q", "events.-1.event").stdout == "stream.opened\n"           # a string: raw
    assert json.loads(r("events", "-q", "events.0").stdout)["seq"] == 0                # anything else: JSON
    assert r("api", "whoami", "-q", "principal_id").stdout.strip() == h["ann"]["principal_id"]
    assert r("status", "-q", "mode").stdout == "remote\n"
    assert r("whoami", "-q", "hosts.0.whoami.principal_id").stdout.strip() == h["ann"]["principal_id"]
    for path in ("nope", "events.9.seq", "events.x", "length.deeper"):
        p = r("stream", "events", "-q", path)
        assert p.returncode == client.EXIT_PARAMS and "--field" in p.stderr, path
    assert client.pick({"a": [{"b": None}]}, "a.0.b") is None
