# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Stored tokens and settings: `auth login|logout|status|rotate` against a real `serve` on a SQLite file, the token's
precedence, `--principal`, a token never sent to another host, a loose credentials file refused, the keychain (a fake
in-memory backend, when the keyring library is installed) and the file without it, and `config`. Every test has a
config directory of its own; none touches ~/.provenstream or the system keychain."""
import io, json, os, re, stat, subprocess, sys, threading, urllib.request
from http.server import BaseHTTPRequestHandler, HTTPServer

import pytest

from conftest import U
from test_client import BIN, free_port

from provenstream import auth, cli, client, config, mode


def ps(cfg, *args, env=None, stdin=None):
    """The command line with config directory `cfg`, no PROVENSTREAM_ settings but `env`, and `stdin` piped in."""
    e = {k: v for k, v in os.environ.items() if not k.startswith("PROVENSTREAM_")}
    e["PROVENSTREAM_CONFIG_DIR"] = str(cfg)
    e.update(env or {})
    return subprocess.run([BIN] + list(args), capture_output=True, text=True, env=e, input=stdin or "")


@pytest.fixture
def sqlite_host(engines, tmp_path):
    """A running `serve` on a temporary SQLite store, with two principals, ann and cy ({principal_id, token} each, from
    the operator's `host principal create`): {"url", "db", "ann", "cy", "cfg"} (cfg: an empty config directory for the
    test)."""
    db = "sqlite:///" + str(tmp_path / "streams.db").lstrip("/")
    cfg = tmp_path / "config"

    def principal():
        return json.loads(subprocess.run([BIN, "host", "principal", "create", "--db", db], capture_output=True,
                                         text=True, check=True).stdout)
    ann, cy = principal(), principal()
    port = free_port()
    srv = subprocess.Popen([BIN, "serve", "--db", db, "--engines", engines["dir"], "--port", str(port)],
                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    url = "http://127.0.0.1:%d" % port
    for _ in range(100):
        try:
            urllib.request.urlopen(url + "/healthz", timeout=1)
            break
        except OSError:
            import time
            time.sleep(0.1)
    yield {"url": url, "db": db, "ann": ann, "cy": cy, "cfg": cfg}
    srv.terminate()
    srv.wait(10)


def creds(cfg):
    with open(os.path.join(str(cfg), "credentials.json")) as f:
        return json.load(f)


def whoami(h, *args, env=None):
    p = ps(h["cfg"], "call", "whoami", "--base-url", h["url"], *args, env=env)
    return p.returncode, (json.loads(p.stdout)["principal_id"] if p.returncode == 0 else p.stderr)


def no_secret(p, *tokens):
    for t in tokens:
        assert t not in p.stdout and t not in p.stderr


# -- login, the token's precedence, principals ----------------------------------------------------------------------

def test_login_stores_and_verifies(sqlite_host, engines):
    h, ann = sqlite_host, sqlite_host["ann"]
    p = ps(h["cfg"], "login", "--base-url", h["url"] + "/", stdin=ann["token"] + "\n")
    assert p.returncode == 0, p.stderr
    assert "logged in to %s as %s;" % (h["url"], ann["principal_id"]) in p.stdout
    assert "cannot be shown again" in p.stdout and "credentials.json" in p.stderr       # the no-keychain warning
    no_secret(p, ann["token"])
    assert stat.S_IMODE(os.stat(h["cfg"]).st_mode) == 0o700
    assert stat.S_IMODE(os.stat(h["cfg"] / "credentials.json").st_mode) == 0o600
    c = creds(h["cfg"])[h["url"]]
    assert c["active"] == ann["principal_id"] and c["principals"][ann["principal_id"]] == {
        "storage": "file", "token": ann["token"]}
    # every remote command now sends it, with no token named
    p = ps(h["cfg"], "open", engines["urls"]["tasks"], "--base-url", h["url"])
    assert p.returncode == 0 and json.loads(p.stdout)["seq"] == 0, p.stderr
    d = json.loads(ps(h["cfg"], "mode", "--json", "--base-url", h["url"]).stdout)
    assert d["token_source"] == "file" and d["stored_principal"] == ann["principal_id"]
    assert d["principal"]["principal_id"] == ann["principal_id"]
    p = ps(h["cfg"], "whoami", "--base-url", h["url"])
    assert p.returncode == 0 and "logged in as %s, token from file" % ann["principal_id"] in p.stdout
    no_secret(p, ann["token"])


def test_a_bad_token_stores_nothing(sqlite_host):
    h = sqlite_host
    p = ps(h["cfg"], "login", "--base-url", h["url"], stdin="ps_not-a-token\n")
    assert p.returncode == client.EXIT_UNAUTHORIZED and "unauthorized" in p.stderr
    assert not (h["cfg"] / "credentials.json").exists()
    p = ps(h["cfg"], "login", "--base-url", h["url"], stdin="\n")
    assert p.returncode == client.EXIT_UNAUTHORIZED and "no token" in p.stderr


def test_login_from_a_token_file_and_default_host(sqlite_host, tmp_path):
    h = sqlite_host
    tf = tmp_path / "t"
    tf.write_text(h["cy"]["token"] + "\n")
    p = ps(h["cfg"], "login", "--base-url", h["url"], "--token-file", str(tf), "--default")
    assert p.returncode == 0 and "default host" in p.stdout, p.stderr
    assert json.loads((h["cfg"] / "config.json").read_text())["default_host"] == h["url"]
    p = ps(h["cfg"], "call", "whoami")                  # no host named: the configured one
    assert p.returncode == 0 and json.loads(p.stdout)["principal_id"] == h["cy"]["principal_id"], p.stderr


def test_env_beats_stored_and_principal_selects(sqlite_host, tmp_path):
    h, ann, cy = sqlite_host, sqlite_host["ann"], sqlite_host["cy"]
    assert ps(h["cfg"], "login", "--base-url", h["url"], stdin=ann["token"]).returncode == 0
    assert ps(h["cfg"], "login", "--base-url", h["url"], stdin=cy["token"]).returncode == 0
    c = creds(h["cfg"])[h["url"]]
    assert c["active"] == cy["principal_id"] and set(c["principals"]) == {ann["principal_id"], cy["principal_id"]}
    assert whoami(h) == (0, cy["principal_id"])                                  # the active principal: the last login
    assert whoami(h, "--principal", ann["principal_id"]) == (0, ann["principal_id"])
    assert whoami(h, env={"PROVENSTREAM_TOKEN": ann["token"]}) == (0, ann["principal_id"])     # env beats stored
    tf = tmp_path / "t"
    tf.write_text(cy["token"])
    assert whoami(h, "--token-file", str(tf), env={"PROVENSTREAM_TOKEN": ann["token"]}) == (0, cy["principal_id"])
    # --principal picks a stored token: an error beside a token named otherwise
    code, err = whoami(h, "--principal", ann["principal_id"], env={"PROVENSTREAM_TOKEN": ann["token"]})
    assert code == client.EXIT_PARAMS and "--principal" in err
    code, err = whoami(h, "--principal", ann["principal_id"], "--token-file", str(tf))
    assert code == client.EXIT_PARAMS
    code, err = whoami(h, "--principal", U("nobody"))
    assert code == client.EXIT_UNAUTHORIZED and "no stored token" in err
    # logging in again switches the active principal back
    assert ps(h["cfg"], "login", "--base-url", h["url"], stdin=ann["token"]).returncode == 0
    assert whoami(h) == (0, ann["principal_id"])
    p = ps(h["cfg"], "auth", "status", "--base-url", h["url"], "--json")
    st = json.loads(p.stdout)["hosts"][0]
    assert st["active"] == ann["principal_id"] and st["token_source"] == "file" and \
        st["whoami"] == {"principal_id": ann["principal_id"]}
    assert st["principals"] == sorted([ann["principal_id"], cy["principal_id"]])
    no_secret(p, ann["token"], cy["token"])


# -- a stored token goes only to its own host -----------------------------------------------------------------------

class Recorder(BaseHTTPRequestHandler):
    seen: list = []
    redirect_to = None

    def do_POST(self):
        Recorder.seen.append(dict(self.headers))
        if Recorder.redirect_to:
            self.send_response(307)
            self.send_header("Location", Recorder.redirect_to + "/rpc")
            self.end_headers()
            return
        self.send_response(500)
        self.end_headers()

    def log_message(self, *a):
        pass


def serve_recorder():
    srv = HTTPServer(("127.0.0.1", free_port()), Recorder)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    return srv, "http://127.0.0.1:%d" % srv.server_address[1]


def test_a_stored_token_is_never_sent_to_another_host(sqlite_host, monkeypatch):
    h, ann = sqlite_host, sqlite_host["ann"]
    assert ps(h["cfg"], "login", "--base-url", h["url"], stdin=ann["token"]).returncode == 0
    other, other_url = serve_recorder()
    Recorder.seen, Recorder.redirect_to = [], None
    try:
        p = ps(h["cfg"], "call", "whoami", "--base-url", other_url)
        assert p.returncode == client.EXIT_UNAUTHORIZED and "no token for %s" % other_url in p.stderr
        assert Recorder.seen == []
        # a host that redirects elsewhere: the client does not follow, so the token stays with the host it is for
        target, target_url = serve_recorder()
        Recorder.redirect_to = target_url
        monkeypatch.setenv("PROVENSTREAM_CONFIG_DIR", str(h["cfg"]))
        auth.put(config.normalize_host(other_url), ann["principal_id"], ann["token"], "file")
        p = ps(h["cfg"], "call", "whoami", "--base-url", other_url)
        assert p.returncode == client.EXIT_UNAVAILABLE and "HTTP 307" in p.stderr, p.stderr
        assert len(Recorder.seen) == 1                       # the redirecting host's request, and no other
        target.shutdown()
    finally:
        Recorder.redirect_to = None
        other.shutdown()


# -- logout, rotate, status -----------------------------------------------------------------------------------------

def test_logout(sqlite_host):
    h, ann, cy = sqlite_host, sqlite_host["ann"], sqlite_host["cy"]
    for t in (ann["token"], cy["token"]):
        assert ps(h["cfg"], "login", "--base-url", h["url"], stdin=t).returncode == 0
    p = ps(h["cfg"], "logout", "--base-url", h["url"])                      # the active one: cy
    assert p.returncode == 0 and "still valid on the host until rotated" in p.stdout, p.stderr
    assert "active now: %s" % ann["principal_id"] in p.stdout and "PROVENSTREAM_TOKEN" not in p.stderr
    assert whoami(h) == (0, ann["principal_id"])
    assert whoami(h, env={"PROVENSTREAM_TOKEN": cy["token"]}) == (0, cy["principal_id"])     # still valid on the host
    p = ps(h["cfg"], "auth", "logout", "--base-url", h["url"], "--all", env={"PROVENSTREAM_TOKEN": cy["token"]})
    assert p.returncode == 0 and "PROVENSTREAM_TOKEN is set and is not affected" in p.stderr
    assert creds(h["cfg"]) == {}
    code, err = whoami(h)
    assert code == client.EXIT_UNAUTHORIZED and "provenstream login" in err
    p = ps(h["cfg"], "logout", "--base-url", h["url"])
    assert p.returncode == 1 and "not logged in" in p.stderr


def test_rotate_saves_the_new_token(sqlite_host):
    h, ann = sqlite_host, sqlite_host["ann"]
    assert ps(h["cfg"], "login", "--base-url", h["url"], stdin=ann["token"]).returncode == 0
    p = ps(h["cfg"], "auth", "rotate", "--base-url", h["url"])
    assert p.returncode == 0 and "rotated the token of %s" % ann["principal_id"] in p.stdout, p.stderr
    new = creds(h["cfg"])[h["url"]]["principals"][ann["principal_id"]]["token"]
    assert new != ann["token"]
    no_secret(p, ann["token"], new)
    assert stat.S_IMODE(os.stat(h["cfg"] / "credentials.json").st_mode) == 0o600
    assert whoami(h) == (0, ann["principal_id"])                                 # the stored, new one
    code, _ = whoami(h, env={"PROVENSTREAM_TOKEN": ann["token"]})
    assert code == client.EXIT_UNAUTHORIZED                                   # the old one, revoked
    junk = h["cfg"] / "junk.token"
    junk.write_text("x")
    p = ps(h["cfg"], "--token-file", str(junk), "auth", "rotate", "--base-url", h["url"])
    assert p.returncode == client.EXIT_PARAMS


def test_rotate_when_the_new_token_cannot_be_saved(sqlite_host, monkeypatch, capsys):
    h, ann = sqlite_host, sqlite_host["ann"]
    monkeypatch.setenv("PROVENSTREAM_CONFIG_DIR", str(h["cfg"]))
    auth.put(config.normalize_host(h["url"]), ann["principal_id"], ann["token"], "file")
    real, calls = auth.put, []

    def failing_put(*args, **kw):
        calls.append(args[3])
        if len(calls) > 1:                        # the check before rotating passes, the save after it fails
            raise OSError("disk full")
        return real(*args, **kw)
    monkeypatch.setattr(auth, "put", failing_put)
    assert cli.main(["auth", "rotate", "--base-url", h["url"]]) == 1
    out, err = capsys.readouterr()
    assert "already revoked" in err and "token rotate %s" % ann["principal_id"] in err and "rotated the" not in out
    assert all(t not in out + err for t in calls)
    code, _ = whoami(h, env={"PROVENSTREAM_TOKEN": ann["token"]})
    assert code == client.EXIT_UNAUTHORIZED                                   # the old token was revoked


def test_status_exit_codes(sqlite_host, monkeypatch):
    h, ann, cy = sqlite_host, sqlite_host["ann"], sqlite_host["cy"]
    p = ps(h["cfg"], "whoami", "--base-url", h["url"])
    assert p.returncode == client.EXIT_UNAUTHORIZED and "no token" in p.stdout
    assert ps(h["cfg"], "login", "--base-url", h["url"], stdin=ann["token"]).returncode == 0
    # a second host, stored by hand: listed when no --base-url is given
    monkeypatch.setenv("PROVENSTREAM_CONFIG_DIR", str(h["cfg"]))
    auth.put("http://127.0.0.1:9", cy["principal_id"], cy["token"], "file", make_active=True)
    p = ps(h["cfg"], "auth", "status", "--json", env={"PROVENSTREAM_BASE_URL": h["url"]})
    d = json.loads(p.stdout)
    assert p.returncode == 0 and [x["host"] for x in d["hosts"]] == [h["url"], "http://127.0.0.1:9"]
    assert d["hosts"][0]["ok"] and not d["hosts"][1]["ok"]
    p = ps(h["cfg"], "auth", "status", env={"PROVENSTREAM_BASE_URL": h["url"]})
    assert p.returncode == client.EXIT_UNAVAILABLE and "(the resolved host)" in p.stdout
    # the operator rotates ann's token on the host's database: the stored one fails
    subprocess.run([BIN, "token", "rotate", ann["principal_id"], "--db", h["db"]], capture_output=True, check=True)
    p = ps(h["cfg"], "whoami", "--base-url", h["url"])
    assert p.returncode == client.EXIT_UNAUTHORIZED and "unauthorized" in p.stdout
    p = ps(h["cfg"], "whoami", "--base-url", h["url"], "--json")
    assert p.returncode == 0 and json.loads(p.stdout)["hosts"][0]["ok"] is False
    p = ps(h["cfg"], "whoami", "--base-url", h["url"], env={"PROVENSTREAM_TOKEN": cy["token"]})
    assert p.returncode == 0 and "token from env" in p.stdout and "PROVENSTREAM_TOKEN is set" in p.stdout


def test_a_loose_credentials_file_is_refused(sqlite_host):
    h, ann = sqlite_host, sqlite_host["ann"]
    assert ps(h["cfg"], "login", "--base-url", h["url"], stdin=ann["token"]).returncode == 0
    os.chmod(h["cfg"] / "credentials.json", 0o644)
    for args in (["call", "whoami", "--base-url", h["url"]], ["whoami", "--json"], ["mode"]):
        p = ps(h["cfg"], *args)
        assert p.returncode == client.EXIT_UNAUTHORIZED and "chmod 600" in p.stderr, (args, p.stderr)
        no_secret(p, ann["token"])
    os.chmod(h["cfg"] / "credentials.json", 0o600)
    assert whoami(h) == (0, ann["principal_id"])


def test_a_token_never_reaches_argv_or_output(sqlite_host, monkeypatch, capsys):
    """In process, so every program started could be seen: login and rotate start none, and print no token."""
    h, ann = sqlite_host, sqlite_host["ann"]
    monkeypatch.setenv("PROVENSTREAM_CONFIG_DIR", str(h["cfg"]))
    started = []
    monkeypatch.setattr(subprocess, "Popen", lambda *a, **k: started.append(a) or (_ for _ in ()).throw(OSError()))
    for name in ("execv", "execvp", "execve", "system", "posix_spawn", "posix_spawnp"):
        if hasattr(os, name):
            monkeypatch.setattr(os, name, lambda *a, **k: started.append(a))
    monkeypatch.setattr(sys, "stdin", io.StringIO(ann["token"] + "\n"))
    assert cli.main(["login", "--base-url", h["url"]]) == 0
    assert cli.main(["auth", "rotate", "--base-url", h["url"]]) == 0
    assert cli.main(["whoami", "--base-url", h["url"]]) == 0
    new = creds(h["cfg"])[h["url"]]["principals"][ann["principal_id"]]["token"]
    out, err = capsys.readouterr()
    assert started == [] and ann["token"] not in out + err and new not in out + err


# -- the keychain ---------------------------------------------------------------------------------------------------

def test_storage_keyring_needs_a_keychain(sqlite_host, monkeypatch, capsys):
    h = sqlite_host
    monkeypatch.setenv("PROVENSTREAM_CONFIG_DIR", str(h["cfg"]))
    monkeypatch.setattr(auth, "keyring_backend", lambda: None)
    monkeypatch.setattr(sys, "stdin", io.StringIO(h["ann"]["token"]))
    assert cli.main(["login", "--base-url", h["url"], "--storage", "keyring"]) == 1
    assert "no keychain" in capsys.readouterr().err and not (h["cfg"] / "credentials.json").exists()


@pytest.fixture
def fake_keyring():
    keyring = pytest.importorskip("keyring")
    from keyring.backend import KeyringBackend

    class Memory(KeyringBackend):
        priority = 1
        store: dict = {}

        def get_password(self, service, user):
            return self.store.get((service, user))

        def set_password(self, service, user, password):
            self.store[(service, user)] = password

        def delete_password(self, service, user):
            self.store.pop((service, user))
    old = keyring.get_keyring()
    keyring.set_keyring(Memory())
    yield Memory.store
    keyring.set_keyring(old)


def test_keyring_storage(sqlite_host, fake_keyring, monkeypatch, capsys):
    h, ann, cy = sqlite_host, sqlite_host["ann"], sqlite_host["cy"]
    monkeypatch.setenv("PROVENSTREAM_CONFIG_DIR", str(h["cfg"]))
    monkeypatch.setattr(sys, "stdin", io.StringIO(ann["token"]))
    assert cli.main(["login", "--base-url", h["url"]]) == 0
    out, err = capsys.readouterr()
    assert "the keychain (service provenstream:%s" % h["url"] in out and "warning" not in err
    assert fake_keyring[("provenstream:" + h["url"], ann["principal_id"])] == ann["token"]
    entry = creds(h["cfg"])[h["url"]]["principals"][ann["principal_id"]]
    assert entry == {"storage": "keyring"}                                    # no token in the file
    assert cli.main(["call", "whoami", "--base-url", h["url"]]) == 0
    assert json.loads(capsys.readouterr().out)["principal_id"] == ann["principal_id"]
    assert cli.main(["auth", "rotate", "--base-url", h["url"]]) == 0
    assert fake_keyring[("provenstream:" + h["url"], ann["principal_id"])] != ann["token"]
    assert cli.main(["call", "whoami", "--base-url", h["url"]]) == 0
    # --storage file forces the file, even with a keychain
    monkeypatch.setattr(sys, "stdin", io.StringIO(cy["token"]))
    assert cli.main(["login", "--base-url", h["url"], "--storage", "file"]) == 0
    assert creds(h["cfg"])[h["url"]]["principals"][cy["principal_id"]]["token"] == cy["token"]
    assert cli.main(["logout", "--base-url", h["url"], "--all"]) == 0
    assert not any(k[0] == "provenstream:" + h["url"] for k in fake_keyring)


def test_the_null_backend_means_the_file(monkeypatch):
    keyring = pytest.importorskip("keyring")
    import keyring.backends.null
    old = keyring.get_keyring()
    keyring.set_keyring(keyring.backends.null.Keyring())
    try:
        assert auth.keyring_backend() is None
    finally:
        keyring.set_keyring(old)


# -- modes and config -----------------------------------------------------------------------------------------------

def test_principal_and_auth_in_local_mode_are_exit_8(tmp_path):
    db = str(tmp_path / "x.db")
    for args in (["head", "s", "--db", db, "--principal", U("ann")], ["call", "whoami", "--principal", U("ann")],
                 ["login", "--db", db], ["auth", "status", "--db", db], ["whoami"], ["logout"]):
        env = {"PROVENSTREAM_DATABASE_URL": db} if "--db" not in args else {}
        p = ps(tmp_path / "cfg", *args, env=env, stdin="x")
        assert p.returncode == client.EXIT_MODE and "rule" in p.stderr, (args, p.stderr)
    p = ps(tmp_path / "cfg", "head", "s", "--as", U("ann"), "--base-url", "http://h")
    assert p.returncode == client.EXIT_MODE                                    # --as in remote mode, as before


def test_default_host_never_selects_remote(tmp_path, monkeypatch):
    import site
    cfg = tmp_path / "cfg"
    assert ps(cfg, "config", "set", "default_host", "HTTP://Example.Test:80/x/").returncode == 0
    assert json.loads((cfg / "config.json").read_text()) == {"default_host": "http://example.test/x"}
    home = {"HOME": str(tmp_path), "PYTHONUSERBASE": site.getuserbase()}
    p = ps(cfg, "host", "principal", "create", env=home)        # local only: the default database
    assert p.returncode == 0, p.stderr
    assert (tmp_path / ".provenstream" / "streams.db").exists()
    d = json.loads(ps(cfg, "mode", "--json").stdout)
    assert d["mode"] == "remote" and d["target"] == "http://example.test/x" and d["host_from"] == "config default_host"
    d = json.loads(ps(cfg, "mode", "--json", env={"PROVENSTREAM_BASE_URL": "http://e.test"}).stdout)
    assert d["target"] == "http://e.test" and d["host_from"] == "PROVENSTREAM_BASE_URL"
    r = mode.resolve(None, None, None, {}, local_only=True, default_host="http://example.test")
    assert r.mode == "local"
    assert mode.resolve(None, None, None, {}, default_host="http://c.test").base_url == "http://c.test"


def test_config(tmp_path):
    cfg, eng = tmp_path / "cfg", tmp_path / "engines"
    p = ps(cfg, "config", "list")
    lines = {l.split()[0]: re.split(r"\s{2,}", l.strip()) for l in p.stdout.splitlines()[1:-1]}
    assert p.returncode == 0 and lines["default_host"][1:] == [client.DEFAULT_BASE_URL, "default"]
    assert lines["local.engines"][1:] == ["<not set>", "default"]
    assert ps(cfg, "config", "set", "local.engines", str(eng)).returncode == 0
    assert ps(cfg, "config", "set", "default_host", "https://h.test").returncode == 0
    p = ps(cfg, "config", "list")
    assert "https://h.test" in p.stdout and p.stdout.count(" config") == 2
    p = ps(cfg, "config", "list", env={"PROVENSTREAM_BASE_URL": "http://e.test"})
    assert "http://e.test" in p.stdout and "env (PROVENSTREAM_BASE_URL)" in p.stdout
    p = ps(cfg, "--base-url", "http://f.test", "config", "list")
    assert "http://f.test" in p.stdout and " flag" in p.stdout
    p = ps(cfg, "config", "list", "--engines", "/e")
    assert "/e " in p.stdout
    assert ps(cfg, "config", "get", "default_host").stdout.strip() == "https://h.test"
    assert ps(cfg, "config", "get", "local.engines").stdout.strip() == str(eng)
    # local.engines is the engines directory when none is named
    assert json.loads(ps(cfg, "mode", "--json", "--db", str(tmp_path / "x.db")).stdout)["engines"] == str(eng)
    d = json.loads(ps(cfg, "mode", "--json", "--db", str(tmp_path / "x.db"), env={"PROVENSTREAM_ENGINES": "/x"}).stdout)
    assert d["engines"] == "/x"
    assert ps(cfg, "config", "unset", "default_host").returncode == 0
    p = ps(cfg, "config", "get", "default_host")
    assert p.returncode == 1 and "not set" in p.stderr
    for args in (["set", "nope", "x"], ["get", "nope"], ["unset", "nope"], ["set", "default_host", "ftp://x"],
                 ["set", "default_host", "not a url"]):
        p = ps(cfg, "config", *args)
        assert p.returncode == client.EXIT_PARAMS and "invalid params" in p.stderr, (args, p.stderr)


def test_normalize_host():
    n = config.normalize_host
    assert n("HTTPS://Streams.Example:443/") == "https://streams.example"
    assert n("http://h:80") == "http://h" and n("http://h:8080/a/b/") == "http://h:8080/a/b"
    assert n("https://u:p@h.test/x?q=1#f") == "https://h.test/x"
    assert n("http://[::1]:9/") == "http://[::1]:9"
    with pytest.raises(client.ClientError):
        n("h.test")
