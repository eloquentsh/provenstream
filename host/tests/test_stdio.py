# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The stdio carrier's environment, where no conformance sequence reaches: framing (in process, on bytes: empty lines,
`\r\n`, over-long lines cut off), and `provenstream serve --stdio` as a process: answers in order, one per line,
flushed, a line that is not JSON, the end of input, an operator session (`--as`), the session's principal named once,
and a session driven from POSIX sh (stdio_session.sh). A token session's answers, and that they are the HTTP carrier's
bytes, are the conformance suite's (`provenstream conform --compare`)."""
import io, json, os, subprocess

import pytest

from conftest import HERE, U
from test_client import BIN

from provenstream import protocol, stdio
from provenstream.host import Operator


def req(method, params=None, rid=1):
    return {"jsonrpc": "2.0", "id": rid, "method": method, "params": params or {}}


def line(method, params=None, rid=1):
    return json.dumps(req(method, params, rid), separators=(",", ":")).encode() + b"\n"


class Echo:
    """A host stand-in for framing: answers each body with its length."""

    def __init__(self):
        self.seen = []

    def handle(self, body, auth):
        self.seen.append(body)
        return protocol.ok(len(body))


def test_framing_in_process():
    h, out = Echo(), io.BytesIO()
    data = b"abc\n\nde\r\n" + b"x" * 20 + b"\n" + b"y" * 11 + b"\nlast"
    assert stdio.serve(h, Operator(None), io.BytesIO(data), out, max_line=10) == 0
    got = [json.loads(x) for x in out.getvalue().splitlines()]
    assert h.seen == [b"abc", b"de", b"last"]                           # \r\n is a newline; an empty line no request
    assert [g.get("result") for g in got] == [3, 2, None, None, 4]
    for g in got[2:4]:                                                    # over-long: cut off, or one byte over
        assert g["id"] is None and g["error"]["data"] == {"code": "invalid_request", "detail": "message over 10 bytes"}
    out = io.BytesIO()
    stdio.serve(Echo(), Operator(None), io.BytesIO(b"x" * 10 + b"\r\n" + b"z" * 12), out, max_line=10)
    assert [json.loads(x).get("result") for x in out.getvalue().splitlines()] == [10, None]   # exactly the limit fits
    out = io.BytesIO()
    assert stdio.serve(Echo(), Operator(None), io.BytesIO(b""), out) == 0 and out.getvalue() == b""


def clean_env():
    return {k: v for k, v in os.environ.items() if not k.startswith("PROVENSTREAM_")}


@pytest.fixture
def db(tmp_path):
    return "sqlite:///" + str(tmp_path / "streams.db").lstrip("/")


def principal(db):
    """{principal_id, token} of a new principal, from the operator's `host principal create` (its token on stdout,
    since no --token-file is given: the operator's own terminal)."""
    p = subprocess.run([BIN, "host", "principal", "create", "--db", db], capture_output=True, text=True,
                       env=clean_env(), check=True)
    return json.loads(p.stdout)


class Session:
    """`provenstream serve --stdio` as a process, asked one line at a time."""

    def __init__(self, db, engines, *auth):
        self.p = subprocess.Popen([BIN, "serve", "--stdio", "--db", db, "--engines", engines["dir"]] + list(auth),
                                  stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                  env=clean_env())

    def send(self, raw: bytes) -> bytes:
        self.p.stdin.write(raw)
        self.p.stdin.flush()
        return self.p.stdout.readline()

    def ask(self, method, params=None, rid=1):
        return json.loads(self.send(line(method, params, rid)))

    def end(self):
        self.p.stdin.close()
        code = self.p.wait(30)
        return code, self.p.stdout.read(), self.p.stderr.read().decode()


def test_an_operator_session(db, engines):
    ann, cy = principal(db), principal(db)
    s = Session(db, engines, "--as", ann["principal_id"])
    try:
        opened = s.ask("stream.open", {"proof_revision_url": engines["urls"]["tasks"]}, rid="o")
        assert opened["id"] == "o" and opened["result"]["seq"] == 0
        stream = opened["result"]["event"]["stream_id"]
        assert s.ask("task.open", {"stream_id": stream, "task_id": U("t0")}, 2)["result"]["seq"] == 1
        a = s.ask("task.open", {"stream_id": stream, "task_id": U("t9"), "actor_id": cy["principal_id"]})
        assert a["error"]["data"] == {"code": "refused", "reason": "actor_id_must_match_the_token"}
        # a line that is not JSON, then a request: the session goes on
        bad = json.loads(s.send(b"{not json\n"))
        assert bad["id"] is None and bad["error"]["code"] == -32700
        assert s.ask("whoami", rid=3) == {"jsonrpc": "2.0", "id": 3, "result": {"principal_id": ann["principal_id"]}}
        # an over-long line: invalid_request with id null, and the next line is answered
        long = json.loads(s.send(b'{"jsonrpc":"2.0","id":9,"method":"whoami","params":{"x":"' +
                                 b"a" * protocol.MAX_BODY + b'"}}\n'))
        assert long["id"] is None and long["error"]["data"]["code"] == "invalid_request"
        # several lines at once: answered in order, one each
        s.p.stdin.write(b"".join(line("stream.head", {"stream_id": stream}, i) for i in range(5)))
        s.p.stdin.flush()
        got = [json.loads(s.p.stdout.readline()) for _ in range(5)]
        assert [g["id"] for g in got] == list(range(5)) and all(g["result"]["length"] == 2 for g in got)
        assert s.ask("task.open", {"stream_id": stream, "task_id": U("t")}, 7)["result"]["seq"] == 2
    finally:
        code, rest, err = s.end()
    assert code == 0 and rest == b""                                     # end of input: a clean exit, nothing more
    assert "serve:" in err and "stdio" in err                             # logs on stderr only


def test_a_session_names_one_principal(db, engines, tmp_path):
    ann = principal(db)
    tf = tmp_path / "token"
    tf.write_text(ann["token"])
    for auth in ([], ["--as", ann["principal_id"], "--token-file", str(tf)]):
        p = subprocess.run([BIN, "serve", "--stdio", "--db", db, "--engines", engines["dir"]] + auth,
                           capture_output=True, text=True, env=clean_env(), input="")
        assert p.returncode == 5 and "one of them" in p.stderr, auth
    p = subprocess.run([BIN, "serve", "--stdio", "--db", db, "--engines", engines["dir"], "--as", U("nobody")],
                       capture_output=True, text=True, env=clean_env(), input="")
    assert p.returncode == 3 and "no such principal" in p.stderr
    p = subprocess.run([BIN, "serve", "--db", db, "--engines", engines["dir"], "--as", ann["principal_id"]],
                       capture_output=True, text=True, env=clean_env())
    assert p.returncode == 5 and "stdio" in p.stderr                    # HTTP has no session principal


def test_stdio_from_sh(db, engines):
    ann = principal(db)
    p = subprocess.run(["sh", os.path.join(HERE, "stdio_session.sh"), BIN, db, engines["dir"], ann["principal_id"],
                        engines["urls"]["core"]],
                       capture_output=True, text=True, env=clean_env(), timeout=120)
    assert p.returncode == 0 and "stdio_session: ok" in p.stdout, p.stdout + p.stderr
