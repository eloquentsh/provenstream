# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The conformance runner (`provenstream conform`): the cases of conformance/ against a host, on any carrier.

A case is one request and the answer it must get, as a pattern; the cases of one file (a theme) run in order as one
session, so a value an earlier case binds (the stream its `stream.open` minted, a chain head) is there for the later
ones. What a pattern means is conformance/README.md's; in short, a JSON value is matched exactly (object keys as a set,
arrays in order, `1` is not `1.0` or `true`), and a string starting with `$` is a pattern: `$uuid`, `$hex64`,
`$string`, `$int`, `$bool`, `$any` match a shape; `$SHAPE:NAME` matches the shape and binds the value to NAME; `$NAME`
must equal what NAME was bound to. Bound before the first case: the role principals (`$opener`, `$other`, `$third`,
`$outsider`), `$commit`, `$repo`, `$run` (a nonce of the run), and for each of the six proofs served (`core`, `log`,
`principals`, `tasks`, `work`, `tower`) its revision `$rev_P` and URL `$url_P`; against a host this runner made, also `$spare`
(whose token `token.rotate` rotates), `$broken`/`$broken_url` (a revision whose engine is missing) and
`$notiface`/`$notiface_url` (one whose engine does not implement the stream interface). An object with `"$open": true`
may hold keys the pattern does not name, and `{"$contains": [P, ...]}` matches an array holding, for each P, an element
matching it. In a request, `$NAME` is the bound value and `${NAME}` inside a string its text (in an expected answer
too: a string holding `${NAME}` is matched as the text it makes). A case with `"proof"`
needs that proof (or each of a list) served, and is skipped otherwise; a case with `"check": "chain"` is a
`stream.rows` answer whose hash chain the runner also recomputes from the rows (chain.py), from the genesis on.

Targets. A local target is a throwaway host on a store of the run (a fresh SQLite file in a temporary directory, or the
database `--db` names: Postgres too), serving the six proofs' engines of one commit (from `--engines DIR`, else built
from this checkout's HEAD, which takes a while), a revision `BROKEN` whose engine is missing, so that `unavailable` can
be brought about, and a revision `NOTIFACE` whose engine (a small script the runner writes) describes itself as no
engine of the stream interface. The runner issues the role principals itself, through the operator path
(`principal.create`, in process), and a fresh `spare` per run for the `token.rotate` cases. `inprocess` hands each
message's bytes to `Host.handle` as `Token(t)`, exactly what a carrier does; `stdio` runs `provenstream serve --stdio
--token-file` against that store, one session per token; `http` runs `provenstream serve` on a free localhost port
against it. `--base-url URL` is a host somebody else runs: principals come from `--tokens FILE` (a JSON object, role ->
token file path; tokens are read, never printed, and checked with `whoami` to be four distinct principals),
`--revision-url` names the core revision it serves (the other proofs are the same commit's packages, where the host
serves them), and the cases marked `local_only` are skipped. A case asked with no token (`who: none`) is skipped on
stdio, where a session always names its principal.

`--compare` runs every case on inprocess, stdio and http at once, a thread per carrier against the same store, each
with principals and nonce of its own, and requires, besides each passing, that the three answers be the same bytes
after normalising exactly the values the case's pattern leaves open: every position the pattern writes as a binding
(`$SHAPE:NAME`), a reference (`$NAME`), or one of the shapes `$uuid`, `$hex64`, `$any` is replaced by that pattern
text before comparing. These are what differ between runs by design: minted ids, chain heads (which hash a fresh salt),
principals, incident ids, tokens, and the `running` flag of `revisions.list`. Everything else is compared as sent,
`detail` texts and `$string`, `$int` and `$bool` positions included, and each answer must be in the host's canonical
form (`wire.dumps` of what it parses to).

The cases are read from this checkout's conformance/cases, or from `--cases DIR` (an installed package has no checkout
beside it), and `--theme` runs some of them.

Output: a line per failed case (its id, the expected pattern and the answer got, any `token` in it shown as
`<token>`), with `--verbose` a line per case, then a summary per theme (its cases and command sequences, passed,
failed, skipped) and per carrier (its time). The exit code is 0 only if no case failed; 2 is a setup error (no engine,
an unreadable tokens file, two roles that are one principal).
"""
from __future__ import annotations
import argparse, base64, json, logging, os, re, shutil, socket, subprocess, sys, tempfile, threading, time
import urllib.error, urllib.request
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Tuple

from . import chain, ids, protocol, wire

HERE = os.path.dirname(os.path.abspath(__file__))
CHECKOUT = os.path.dirname(os.path.dirname(HERE))
CASES = os.path.join(CHECKOUT, "conformance", "cases")

ROLES = ("opener", "other", "third", "outsider")
UNKNOWN_TOKEN = "ps_conformance-unknown-token"
BROKEN = "bad" * 13 + "b"                       # a revision whose engine is missing (local targets only)
NOTIFACE = "0bad" * 10                          # a revision whose engine is not the stream interface (local only)
PROOFS = {"core": "", "log": "examples/log", "principals": "examples/principals", "tasks": "examples/tasks",
          "work": "examples/work", "tower": "tests/tower"}   # the six proofs, by their package path in one commit
CASE_KEYS = {"id", "who", "method", "params", "rid", "raw", "raw_base64", "oversize", "answer_id", "expect",
             "local_only", "proof", "check"}

NOT_AN_ENGINE = """#!%(python)s
# Written by provenstream conform: an engine that starts and describes itself, and is not the stream interface.
import json, sys
print('{"ready":true}', flush=True)
for line in sys.stdin:
    try:
        q = json.loads(line)
    except ValueError:
        q = None
    if q == {"query": "describe"}:
        out = {"revision": %(revision)r, "package": "", "repo": %(repo)r, "protocol": 2,
               "schema": {"commands": [{"name": "counter.add", "params": [], "minted": [], "fresh": 0,
                                        "stream_id": "stream_id", "event": {"name": "counter.added", "fields": []},
                                        "rules": []}]}}
    elif q == {"query": "revision"}:
        out = {"revision": %(revision)r, "package": "", "repo": %(repo)r}
    else:
        out = {"error": "malformed", "detail": "not a counter command"}
    print(json.dumps(out), flush=True)
"""

NAME = r"[a-z_][a-z0-9_]*"
SHAPES = {
    "any": lambda v: True,
    "uuid": lambda v: isinstance(v, str) and ids.CANONICAL_ID.fullmatch(v) is not None,
    "hex64": lambda v: isinstance(v, str) and re.fullmatch(r"[0-9a-f]{64}", v) is not None,
    "string": lambda v: isinstance(v, str),
    "int": lambda v: isinstance(v, int) and not isinstance(v, bool),
    "bool": lambda v: isinstance(v, bool),
}
VOLATILE = {"any", "uuid", "hex64"}


class SetupError(Exception):
    """The run cannot start: no engine, no tokens, two roles that are one principal (exit 2)."""


class CaseError(Exception):
    """A case file that is not one: an unknown key, an unknown role, a malformed pattern."""


class Mismatch(Exception):
    def __init__(self, path: str, why: str):
        self.path, self.why = path, why
        super().__init__("%s: %s" % (path, why))


class TargetError(Exception):
    """The target gave no answer to read: a session ended, HTTP said other than 200."""


# -- cases ------------------------------------------------------------------------------------------------------------

def load_cases(directory: str, only: Optional[List[str]] = None) -> List[Tuple[str, List[dict]]]:
    """The themes of `directory` (each `THEME.jsonl`), in name order, or only those named."""
    if not os.path.isdir(directory):
        raise SetupError("no cases at %s (pass --cases DIR)" % directory)
    names = sorted(f[:-len(".jsonl")] for f in os.listdir(directory) if f.endswith(".jsonl"))
    if only:
        unknown = sorted(set(only) - set(names))
        if unknown:
            raise SetupError("no such theme: %s (themes: %s)" % (" ".join(unknown), " ".join(names)))
        names = [n for n in names if n in only]
    out, seen = [], set()
    for n in names:
        cases = []
        with open(os.path.join(directory, n + ".jsonl"), encoding="utf-8") as f:
            for i, text in enumerate(f, 1):
                if not text.strip():
                    continue
                try:
                    c = wire.loads(text)
                except wire.BadJson as x:
                    raise CaseError("%s.jsonl:%d: %s" % (n, i, x))
                bad = sorted(set(c) - CASE_KEYS) if isinstance(c, dict) else ["(not an object)"]
                if bad or "id" not in c or "expect" not in c or "who" not in c:
                    raise CaseError("%s.jsonl:%d: a case is {id, who, method|raw|raw_base64|oversize, expect, ...}"
                                    "%s" % (n, i, (": unknown " + " ".join(bad)) if bad else ""))
                if c["id"] in seen:
                    raise CaseError("%s.jsonl:%d: case id %s repeated" % (n, i, c["id"]))
                seen.add(c["id"])
                cases.append(c)
        out.append((n, cases))
    return out


def _pattern(s: str) -> Optional[Tuple[Optional[str], Optional[str]]]:
    """A pattern string's (shape, name), or None for a literal ("$$..." is the literal "$...")."""
    if not s.startswith("$") or s.startswith("$$"):
        return None
    body = s[1:]
    if ":" in body:
        shape, name = body.split(":", 1)
        if shape not in SHAPES or not re.fullmatch(NAME, name):
            raise CaseError("pattern %r: expected $SHAPE:NAME, a shape of %s" % (s, " ".join(SHAPES)))
        return shape, name
    if body in SHAPES:
        return body, None
    if not re.fullmatch(NAME, body):
        raise CaseError("pattern %r: not a shape or a name" % s)
    return None, body


def _same(a: Any, b: Any) -> bool:
    """JSON equality: `1`, `1.0` and `true` are three values."""
    if isinstance(a, dict) and isinstance(b, dict):
        return a.keys() == b.keys() and all(_same(a[k], b[k]) for k in a)
    if isinstance(a, list) and isinstance(b, list):
        return len(a) == len(b) and all(_same(x, y) for x, y in zip(a, b))
    return type(a) is type(b) and a == b


def _show(x: Any, limit: int = 160) -> str:
    s = wire.dumps(x)
    return s if len(s) <= limit else s[:limit] + "..."


def match(p: Any, a: Any, env: Dict[str, Any], path: str = "answer") -> Any:
    """Match answer `a` against pattern `p`, binding into `env`. Answers `a` normalised (each open position the
    pattern names replaced by the pattern's text: see the module's account of `--compare`); raises `Mismatch`."""
    if isinstance(p, str) and "${" in p:                # a text with bound values in it: matched as that text
        want = subst(p, env)
        if not _same(want, a):
            raise Mismatch(path, "expected %s, got %s" % (_show(want), _show(a)))
        return a
    if isinstance(p, str):
        pat = _pattern(p)
        if pat is not None:
            shape, name = pat
            if shape is not None and not SHAPES[shape](a):
                raise Mismatch(path, "expected %s, got %s" % (p, _show(a)))
            if shape is not None and name is None:
                return p if shape in VOLATILE else a
            if shape is None and name not in env:
                raise Mismatch(path, "$%s is unbound (did an earlier case of this theme fail?)" % name)
            if name in env and not _same(env[name], a):
                raise Mismatch(path, "expected $%s = %s, got %s" % (name, _show(env[name]), _show(a)))
            env[name] = a
            return p
        p = p[1:] if p.startswith("$$") else p
    if isinstance(p, dict) and "$contains" in p:
        if set(p) != {"$contains"} or not isinstance(p["$contains"], list):
            raise CaseError("%s: {\"$contains\": [patterns]} takes nothing else" % path)
        if not isinstance(a, list):
            raise Mismatch(path, "expected an array, got %s" % _show(a))
        out, used = list(a), set()
        for q in p["$contains"]:
            for j, x in enumerate(a):
                if j in used:
                    continue
                trial = dict(env)
                try:
                    n = match(q, x, trial, "%s[%d]" % (path, j))
                except Mismatch:
                    continue
                env.update(trial)
                used.add(j)
                out[j] = n
                break
            else:
                raise Mismatch(path, "no element matches %s" % _show(q))
        return out
    if isinstance(p, dict):
        if not isinstance(a, dict):
            raise Mismatch(path, "expected an object, got %s" % _show(a))
        is_open = p.get("$open") is True
        keys = [k for k in p if k != "$open"]
        missing = [k for k in keys if k not in a]
        if missing:
            raise Mismatch(path, "missing %s in %s" % (", ".join(missing), _show(a)))
        extra = [k for k in a if k not in p] if not is_open else []
        if extra:
            raise Mismatch(path, "unexpected %s in %s" % (", ".join(extra), _show(a)))
        return {k: (match(p[k], v, env, "%s.%s" % (path, k)) if k in p else v) for k, v in a.items()}
    if isinstance(p, list):
        if not isinstance(a, list) or len(a) != len(p):
            raise Mismatch(path, "expected an array of %d, got %s" % (len(p), _show(a)))
        return [match(q, x, env, "%s[%d]" % (path, i)) for i, (q, x) in enumerate(zip(p, a))]
    if not _same(p, a):
        raise Mismatch(path, "expected %s, got %s" % (_show(p), _show(a)))
    return a


def subst(x: Any, env: Dict[str, Any]) -> Any:
    """A request with its references filled in: `$NAME` is the bound value, `${NAME}` inside a string its text."""
    if isinstance(x, str):
        m = re.fullmatch(r"\$(%s)" % NAME, x)
        if m:
            if m.group(1) not in env:
                raise Mismatch("request", "$%s is unbound (did an earlier case of this theme fail?)" % m.group(1))
            return env[m.group(1)]

        def one(m: "re.Match") -> str:
            if m.group(1) not in env:
                raise Mismatch("request", "${%s} is unbound" % m.group(1))
            return str(env[m.group(1)])
        return re.sub(r"\$\{(%s)\}" % NAME, one, x)
    if isinstance(x, dict):
        return {k: subst(v, env) for k, v in x.items()}
    if isinstance(x, list):
        return [subst(v, env) for v in x]
    return x


def message(c: dict, rid: Any, env: Dict[str, Any]) -> Tuple[bytes, Any]:
    """The bytes a case sends, and the id its answer must carry."""
    if "raw" in c:
        return c["raw"].encode("utf-8"), c.get("answer_id")
    if "raw_base64" in c:
        return base64.b64decode(c["raw_base64"]), c.get("answer_id")
    if c.get("oversize"):
        pad = "a" * protocol.MAX_BODY
        return wire.dumps({"jsonrpc": "2.0", "id": 1, "method": "whoami", "params": {"pad": pad}}).encode(), \
            c.get("answer_id")
    if "method" not in c:
        raise CaseError("%s: no method, raw, raw_base64 or oversize" % c["id"])
    msg: Dict[str, Any] = {"jsonrpc": "2.0", "id": rid, "method": c["method"]}
    if "params" in c:
        msg["params"] = subst(c["params"], env)
    return wire.dumps(msg).encode("utf-8"), rid


def redact(x: Any) -> Any:
    if isinstance(x, dict):
        return {k: ("<token>" if k == "token" and isinstance(v, str) else redact(v)) for k, v in x.items()}
    if isinstance(x, list):
        return [redact(v) for v in x]
    return x


# -- targets ----------------------------------------------------------------------------------------------------------

def _child_env() -> Dict[str, str]:
    env = {k: v for k, v in os.environ.items() if not k.startswith("PROVENSTREAM_")}
    pkg_parent = os.path.dirname(HERE)
    env["PYTHONPATH"] = pkg_parent + (os.pathsep + env["PYTHONPATH"] if env.get("PYTHONPATH") else "")
    return env


def _cli() -> List[str]:
    return [sys.executable, "-m", "provenstream"]


class Fixture:
    """A throwaway host's state: a temporary directory holding an engines directory (the six proofs of one commit, the
    broken revision and the one not of the interface) and, unless `db` names one, a SQLite store. The role principals
    are issued per run, through the operator path (`local_run`)."""

    def __init__(self, engines_dir: Optional[str], commit: Optional[str], say=print, db: Optional[str] = None):
        from .revisions import load_map, revision_url, split_key, stamped_repo
        self.tmp = tempfile.mkdtemp(prefix="provenstream-conform-")
        try:
            if engines_dir is None:
                engines_dir = self._build(say)
            m = load_map(os.path.join(engines_dir, "revisions.json"))
            self.commit = commit or self._commit(m, engines_dir)
            self.revisions: Dict[str, str] = {}            # proof -> revision key
            engines: Dict[str, str] = {}
            for proof, package in PROOFS.items():
                key = self.commit + ("/" + package if package else "")
                if key in m:
                    self.revisions[proof] = key
                    engines[key] = m[key][0]
            if "core" not in self.revisions:
                raise SetupError("%s serves no core revision at %s" % (engines_dir, self.commit))
            command = m[self.revisions["core"]]
            repo = stamped_repo(_describe(command), command)
            if repo is None:
                raise SetupError("the core engine of %s does not say which repository it was built from" % self.commit)
            self.repo = repo.rstrip("/")
            self.urls = {p: revision_url(self.repo, *split_key(k)) for p, k in self.revisions.items()}
            self.edir = os.path.join(self.tmp, "engines")
            os.makedirs(self.edir)
            fake = os.path.join(self.edir, "not-an-engine")
            with open(fake, "w", encoding="utf-8") as f:
                f.write(NOT_AN_ENGINE % {"python": sys.executable, "revision": NOTIFACE, "repo": self.repo})
            os.chmod(fake, 0o755)
            engines.update({BROKEN: os.path.join(self.edir, "missing", "engine"), NOTIFACE: fake})
            with open(os.path.join(self.edir, "revisions.json"), "w", encoding="utf-8") as f:
                json.dump({"engines": engines}, f, indent=2)
            self.db = db or "sqlite:///" + os.path.join(self.tmp, "streams.db").lstrip("/")
            from .store import open_store
            open_store(self.db).close()                 # its tables made once, before the carriers open it at once
        except BaseException:
            self.close()
            raise

    def _build(self, say) -> str:
        from . import build
        if not (os.path.isdir(os.path.join(CHECKOUT, ".git")) and
                os.path.exists(os.path.join(CHECKOUT, "lakefile.toml"))):
            raise SetupError("no checkout to build the engines from: pass --engines DIR")
        say("conform: building the six proofs' engines at HEAD (pass --engines DIR to use some already built)")
        edir = os.path.join(self.tmp, "built")
        try:
            for proof, package in PROOFS.items():
                out = os.path.join(self.tmp, "build-" + proof)
                build.build_engine(CHECKOUT, "HEAD", out, package or ".", reuse_lake=CHECKOUT, say=lambda *a: None)
                build.install(out, edir, say=lambda *a: None)
        except build.BuildFailed as x:
            raise SetupError("building the engines: %s" % x)
        return edir

    @staticmethod
    def _commit(m: Dict[str, List[str]], engines_dir: str) -> str:
        """The commit of `m` that serves the core and the most of the other proofs (one, or name it)."""
        from .revisions import split_key
        score: Dict[str, int] = {}
        for key in m:
            commit, package = split_key(key)
            if package in PROOFS.values():
                score[commit] = score.get(commit, 0) + (100 if not package else 1)
        top = max(score.values()) if score else 0
        best = [c for c, n in score.items() if n >= 100 and n == top]
        if len(best) != 1:
            raise SetupError("%s serves %s commit with the core and the most of the other proofs: name one with "
                             "--revision COMMIT" % (engines_dir, "no" if not best else "more than one"))
        return best[0]

    def issue(self) -> Tuple[str, str]:
        from .host import Host, Operator
        host = Host.open(self.db)
        try:
            got = host.command("principal.create", auth=Operator(None))
        finally:
            host.close()
        return got["principal_id"], got["token"]

    def close(self) -> None:
        shutil.rmtree(self.tmp, ignore_errors=True)


def _describe(command: List[str]) -> dict:
    from .engine import Engine, EngineFailure
    e = Engine(command)
    try:
        e.start()
        return e.describe()
    except (EngineFailure, OSError) as x:
        raise SetupError("the engine %s does not start: %s" % (command[0], x))
    finally:
        e.stop()


class InProcess:
    """`Host.handle` on the message's bytes, as `Token(t)`: what every carrier does, without one."""
    name, no_token = "inprocess", True

    def __init__(self, fx: Fixture):
        from .host import Host
        self.host = Host.open(fx.db, fx.edir)

    def send(self, body: bytes, token: Optional[str]) -> bytes:
        from .host import Token
        return self.host.handle(body, Token(token)).dumps().encode("utf-8")

    def close(self) -> None:
        self.host.close()


class Stdio:
    """`provenstream serve --stdio --token-file F` against the fixture's store: one session per token, started when
    first asked."""
    name, no_token = "stdio", False

    def __init__(self, fx: Fixture):
        self.fx = fx
        self.sessions: Dict[str, subprocess.Popen] = {}
        self.dir = tempfile.mkdtemp(prefix="stdio-", dir=fx.tmp)

    def _session(self, token: str) -> subprocess.Popen:
        p = self.sessions.get(token)
        if p is None:
            n = len(self.sessions)
            tf = os.path.join(self.dir, "token-%d" % n)
            fd = os.open(tf, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
            with os.fdopen(fd, "w") as f:
                f.write(token + "\n")
            log = open(os.path.join(self.dir, "session-%d.log" % n), "wb")
            p = self.sessions[token] = subprocess.Popen(
                _cli() + ["serve", "--stdio", "--db", self.fx.db, "--engines", self.fx.edir, "--token-file", tf],
                stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=log, env=_child_env())
            log.close()
        return p

    def send(self, body: bytes, token: Optional[str]) -> bytes:
        if token is None:
            raise TargetError("a stdio session always names a principal")
        if b"\n" in body:
            raise CaseError("a message for stdio holds a newline")
        p = self._session(token)
        try:
            p.stdin.write(body + b"\n")
            p.stdin.flush()
        except BrokenPipeError:
            raise TargetError("the stdio session ended")
        line = p.stdout.readline()
        if not line.endswith(b"\n"):
            raise TargetError("the stdio session ended without an answer")
        return line[:-1]

    def close(self) -> None:
        for p in self.sessions.values():
            try:
                p.stdin.close()
                p.wait(30)
            except (OSError, subprocess.TimeoutExpired):
                p.kill()
                p.wait()


class Http:
    """POST /rpc with the token as `Authorization: Bearer`: to `provenstream serve` on a free localhost port against
    the fixture's store, or to the host at `url`."""
    name, no_token = "http", True

    def __init__(self, fx: Optional[Fixture] = None, url: Optional[str] = None, timeout: float = 120.0):
        self.proc: Optional[subprocess.Popen] = None
        self.timeout = timeout
        if fx is None:
            self.url = url.rstrip("/")
            self.name = "remote"
            return
        with socket.socket() as s:
            s.bind(("127.0.0.1", 0))
            port = s.getsockname()[1]
        log_path = os.path.join(fx.tmp, "http-%d.log" % port)
        with open(log_path, "wb") as log:
            self.proc = subprocess.Popen(_cli() + ["serve", "--db", fx.db, "--engines", fx.edir, "--host", "127.0.0.1",
                                                   "--port", str(port)], stdout=log, stderr=log, env=_child_env())
        self.url = "http://127.0.0.1:%d" % port
        deadline = time.time() + 60
        while True:
            if self.proc.poll() is not None:
                with open(log_path, encoding="utf-8", errors="replace") as f:
                    raise SetupError("provenstream serve exited %d: %s" % (self.proc.returncode, f.read()[-2000:]))
            try:
                with urllib.request.urlopen(self.url + "/healthz", timeout=2) as r:
                    if r.status == 200:
                        break
            except (urllib.error.URLError, OSError):
                pass
            if time.time() > deadline:
                self.close()
                raise SetupError("provenstream serve did not answer /healthz within 60 s")
            time.sleep(0.1)

    def send(self, body: bytes, token: Optional[str]) -> bytes:
        headers = {"Content-Type": "application/json", "User-Agent": "provenstream-conform"}
        if token is not None:
            headers["Authorization"] = "Bearer " + token
        req = urllib.request.Request(self.url + "/rpc", body, headers)
        try:
            with urllib.request.urlopen(req, timeout=self.timeout) as r:
                return r.read()
        except urllib.error.HTTPError as x:
            raise TargetError("HTTP %d (an answer is always HTTP 200, the outcome in its body)" % x.code)
        except (urllib.error.URLError, OSError) as x:
            raise TargetError("cannot reach %s: %s" % (self.url, getattr(x, "reason", x)))

    def close(self) -> None:
        if self.proc is not None:
            self.proc.terminate()
            try:
                self.proc.wait(30)
            except subprocess.TimeoutExpired:
                self.proc.kill()
                self.proc.wait()
            self.proc = None


LOCAL_TARGETS = {"inprocess": InProcess, "stdio": Stdio, "http": Http}


# -- running ----------------------------------------------------------------------------------------------------------

@dataclass
class Result:
    case: str
    status: str                       # PASS, FAIL or SKIP
    note: str = ""
    normal: Optional[str] = None      # the answer normalised (PASS only)
    raw: Optional[bytes] = None
    expected: Any = None
    got: Any = None


@dataclass
class Run:
    """What one run binds before its first case, and its tokens by role (never printed)."""
    env: Dict[str, Any]
    tokens: Dict[str, str]
    remote: bool


def proof_env(commit: str, repo: str, revisions: Dict[str, str], urls: Dict[str, str]) -> Dict[str, Any]:
    env: Dict[str, Any] = {"commit": commit, "repo": repo}
    for p in revisions:
        env["rev_" + p], env["url_" + p] = revisions[p], urls[p]
    return env


def local_run(fx: Fixture) -> Run:
    """A run's own principals (each carrier of --compare its own) and nonce, on the fixture's host."""
    tokens, principals = {}, {}
    for role in ROLES + ("spare",):
        principals[role], tokens[role] = fx.issue()
    env = dict(principals, broken=BROKEN, broken_url=fx.repo + "/commit/" + BROKEN, notiface=NOTIFACE,
               notiface_url=fx.repo + "/commit/" + NOTIFACE, run=ids.uuid7(),
               **proof_env(fx.commit, fx.repo, fx.revisions, fx.urls))
    return Run(env, tokens, remote=False)


def _token(who: Any, run: Run, env: Dict[str, Any]) -> Optional[str]:
    if who == "none":
        return None
    if who == "unknown":
        return UNKNOWN_TOKEN
    if isinstance(who, str) and who in run.tokens:
        return run.tokens[who]
    if isinstance(who, str) and who.startswith("$") and re.fullmatch(NAME, who[1:]):
        if who[1:] not in env or not isinstance(env[who[1:]], str):
            raise Mismatch("who", "%s is unbound (did an earlier case of this theme fail?)" % who)
        return env[who[1:]]
    raise CaseError("who %r: a role (%s, spare), none, unknown, or $NAME bound to a token"
                    % (who, ", ".join(ROLES)))


def run_cases(target, themes: List[Tuple[str, List[dict]]], run: Run, say=None) -> List[Result]:
    out = []
    for theme, cases in themes:
        env = dict(run.env)
        for i, c in enumerate(cases, 1):
            r = run_case(target, c, i, env, run)
            out.append(r)
            if say:
                say(r)
    return out


def run_case(target, c: dict, index: int, env: Dict[str, Any], run: Run) -> Result:
    cid = c["id"]
    if c.get("local_only") and run.remote:
        return Result(cid, "SKIP", "local_only: needs a host this runner made")
    needs = c.get("proof")
    missing = [p for p in ([needs] if isinstance(needs, str) else needs or []) if "url_" + p not in env]
    if missing:
        return Result(cid, "SKIP", "the host serves no %s revision of this commit" % " or ".join(missing))
    if c["who"] == "none" and not target.no_token:
        return Result(cid, "SKIP", "%s: a session always names a principal" % target.name)
    expected = got = None
    try:
        rid = c.get("rid", index)
        body, answer_id = message(c, rid, env)
        token = _token(c["who"], run, env)
        expected = dict({"jsonrpc": "2.0", "id": answer_id}, **c["expect"])
        raw = target.send(body, token)
        try:
            got = wire.loads(raw)
        except wire.BadJson as x:
            return Result(cid, "FAIL", "the answer is not strict JSON: %s" % x, raw=raw, expected=expected,
                          got=raw.decode("utf-8", "replace"))
        trial = dict(env)
        normal = match(expected, got, trial)
        if c.get("check") == "chain":
            why = chain_problem((subst(c.get("params") or {}, env)).get("stream_id"), got.get("result"))
            if why:
                return Result(cid, "FAIL", "the rows' chain does not recompute: %s" % why, raw=raw,
                              expected=expected, got=got)
        env.update(trial)
        return Result(cid, "PASS", normal=wire.dumps(normal), raw=raw, expected=expected, got=got)
    except Mismatch as x:
        return Result(cid, "FAIL", str(x), expected=expected, got=got)
    except TargetError as x:
        return Result(cid, "FAIL", str(x), expected=expected)


def chain_problem(stream: Any, result: Any) -> Optional[str]:
    """Why the rows of a `stream.rows` answer (all of them, from seq 0) do not chain as chain.py says, or None."""
    if not isinstance(stream, str) or not isinstance(result, dict) or not isinstance(result.get("rows"), list):
        return "not a stream.rows answer of one stream"
    try:
        rows = [chain.row_from_json(r) for r in result["rows"]]
    except (KeyError, TypeError, ValueError, wire.BadJson) as x:
        return "a row is not one: %s" % x
    if [r.seq for r in rows] != list(range(len(rows))):
        return "the rows are not every row from seq 0"
    rep_ = chain.verify(stream, rows)
    return None if rep_.ok else rep_.detail


def _print_fail(r: Result, label: str = "") -> None:
    print("      %swhy:      %s" % (label, r.note))
    if r.expected is not None:
        print("      %sexpected: %s" % (label, wire.dumps(r.expected)))
    if r.got is not None:
        print("      %sgot:      %s" % (label, wire.dumps(redact(r.got)) if not isinstance(r.got, str) else r.got))


def _say(r: Result) -> None:
    print("%s  %s%s" % (r.status, r.case, "  (%s)" % r.note if r.status == "SKIP" else ""), flush=True)
    if r.status == "FAIL":
        _print_fail(r)


def compare(per_target: Dict[str, List[Result]]) -> List[Result]:
    """One result per case over every carrier: PASS when it passed wherever it ran and the normalised answers are the
    same bytes, each in canonical form."""
    names = list(per_target)
    out = []
    for rows in zip(*per_target.values()):
        cid = rows[0].case
        ran = [(n, r) for n, r in zip(names, rows) if r.status != "SKIP"]
        failed = [(n, r) for n, r in ran if r.status == "FAIL"]
        if failed:
            out.append(Result(cid, "FAIL", "; ".join("%s: %s" % (n, r.note) for n, r in failed),
                              expected=failed[0][1].expected, got=failed[0][1].got))
            continue
        if not ran:
            out.append(Result(cid, "SKIP", "; ".join("%s: %s" % (n, r.note) for n, r in zip(names, rows))))
            continue
        bad = [n for n, r in ran if wire.dumps(wire.loads(r.raw)).encode("utf-8") != r.raw]
        if bad:
            out.append(Result(cid, "FAIL", "not in canonical form on %s" % " ".join(bad)))
            continue
        normals = {r.normal for _, r in ran}
        if len(normals) > 1:
            out.append(Result(cid, "FAIL", "carriers differ: " + " | ".join(
                "%s: %s" % (n, json.dumps(redact(json.loads(r.normal)), ensure_ascii=False)) for n, r in ran)))
            continue
        skipped = [n for n, r in zip(names, rows) if r.status == "SKIP"]
        out.append(Result(cid, "PASS", "skipped on %s" % " ".join(skipped) if skipped else "", normal=ran[0][1].normal))
    return out


def _theme(cid: str) -> str:
    return cid.split("/", 1)[0]


def _sequence(cid: str) -> Optional[str]:
    """The command sequence a proof theme's case belongs to (`tasks/g07/03-...` -> `tasks/g07`)."""
    parts = cid.split("/")
    return "/".join(parts[:2]) if len(parts) == 3 else None


def summary(results: List[Result], what: str, times: Optional[Dict[str, float]] = None) -> int:
    themes: Dict[str, Dict[str, Any]] = {}
    for r in results:
        t = themes.setdefault(_theme(r.case), {"cases": 0, "seqs": set(), "PASS": 0, "FAIL": 0, "SKIP": 0})
        t["cases"] += 1
        t[r.status] += 1
        if _sequence(r.case):
            t["seqs"].add(_sequence(r.case))
    print("conform: %-12s %6s %9s %7s %7s %7s" % ("theme", "cases", "sequences", "passed", "failed", "skipped"))
    for name in sorted(themes):
        t = themes[name]
        print("conform: %-12s %6d %9s %7d %7d %7d" % (name, t["cases"], len(t["seqs"]) or "-", t["PASS"], t["FAIL"],
                                                       t["SKIP"]))
    for name, secs in (times or {}).items():
        print("conform: time, %s: %.1f s" % (name, secs))
    n = {s_: sum(1 for r in results if r.status == s_) for s_ in ("PASS", "FAIL", "SKIP")}
    print("conform: %d cases on %s: %d passed, %d failed, %d skipped" % (len(results), what, n["PASS"], n["FAIL"],
                                                                          n["SKIP"]))
    print("conform: %s" % ("FAIL" if n["FAIL"] else "PASS (protocol %d)" % protocol.PROTOCOL_VERSION))
    return 1 if n["FAIL"] else 0


# -- remote ----------------------------------------------------------------------------------------------------------

def remote_run(target: Http, tokens_file: str, revision_url: str) -> Run:
    """The principals of `tokens_file` ({role: token file path}), checked to be four distinct principals; and the six
    proofs at the commit of `revision_url`, as far as the host serves them (`revisions.list`)."""
    from .revisions import parse_url, revision_url as url_of, split_key
    named = parse_url(revision_url)
    if named is None or named.package:
        raise SetupError("--revision-url: the core revision's URL: a repository URL, /commit/ (or # or @) and a full "
                         "commit hash")
    try:
        with open(tokens_file, encoding="utf-8") as f:
            paths = json.load(f)
    except (OSError, ValueError) as x:
        raise SetupError("--tokens %s: %s" % (tokens_file, x))
    missing = [r for r in ROLES if not isinstance(paths, dict) or not isinstance(paths.get(r), str)]
    if missing:
        raise SetupError("--tokens: a JSON object naming a token file for each role (%s); missing: %s"
                         % (", ".join(ROLES), " ".join(missing)))
    base = os.path.dirname(os.path.abspath(tokens_file))
    tokens, principals = {}, {}
    ask = lambda method, tok: wire.loads(target.send(wire.dumps({"jsonrpc": "2.0", "id": 0, "method": method})
                                                     .encode(), tok))
    for role in ROLES:
        path = os.path.join(base, os.path.expanduser(paths[role]))
        try:
            with open(path, encoding="utf-8") as f:
                tok = f.read().strip()
        except OSError as x:
            raise SetupError("--tokens: %s: cannot read its token file: %s" % (role, x.strerror))
        if not tok:
            raise SetupError("--tokens: %s: the token file is empty" % role)
        try:
            ans = ask("whoami", tok)
        except (TargetError, wire.BadJson) as x:
            raise SetupError("whoami as %s: %s" % (role, x))
        got = ans.get("result") if isinstance(ans, dict) else None
        if not isinstance(got, dict) or not isinstance(got.get("principal_id"), str):
            raise SetupError("whoami as %s: the host does not accept its token: %s" % (role, _show(redact(ans))))
        tokens[role], principals[role] = tok, got["principal_id"]
    if len(set(principals.values())) != len(principals):
        raise SetupError("--tokens: the roles must be four distinct principals")
    try:
        listed = ask("revisions.list", tokens["opener"])["result"]["revisions"]
    except (TargetError, wire.BadJson, KeyError, TypeError) as x:
        raise SetupError("revisions.list: %s" % x)
    keys = {r.get("revision") for r in listed if isinstance(r, dict)}
    revisions = {}
    for p, pkg in PROOFS.items():
        k = named.commit + ("/" + pkg if pkg else "")
        if k in keys:
            revisions[p] = k
    if "core" not in revisions:
        raise SetupError("--revision-url: the host does not serve revision %s" % named.commit)
    urls = {p: url_of(named.repo, *split_key(k)) for p, k in revisions.items()}
    env = dict(principals, run=ids.uuid7(), **proof_env(named.commit, named.repo.rstrip("/"), revisions, urls))
    return Run(env, tokens, remote=True)


# -- the command line -------------------------------------------------------------------------------------------------

def add_arguments(s: argparse.ArgumentParser) -> None:
    s.add_argument("--target", choices=sorted(LOCAL_TARGETS), default=None,
                   help="a throwaway host this runner makes, on one carrier (default: inprocess)")
    s.add_argument("--compare", action="store_true",
                   help="every local carrier at once, requiring the same answer bytes up to minted ids, hashes and "
                        "tokens")
    s.add_argument("--base-url", dest="base_url", default=argparse.SUPPRESS,
                   help="a host somebody else runs (needs --tokens and --revision-url)")
    s.add_argument("--tokens", help="--base-url: a JSON object, role -> token file path, for the roles %s: four "
                                    "distinct principals" % ", ".join(ROLES))
    s.add_argument("--revision-url", help="--base-url: the proof URL of the core revision the host serves (its "
                                          "commit's other proofs are used where the host serves them)")
    s.add_argument("--engines", default=argparse.SUPPRESS,
                   help="local targets: an engines directory holding the six proofs' engines of one commit (default: "
                        "PROVENSTREAM_ENGINES, else built from this checkout's HEAD)")
    s.add_argument("--revision", help="local targets: the commit whose proofs to serve from --engines (default: the "
                                      "one that serves the core and the most of the others)")
    s.add_argument("--db", default=argparse.SUPPRESS,
                   help="local targets: the store (a Postgres connection string, or a SQLite path; default: a fresh "
                        "SQLite file of the run). The run adds streams and principals to it")
    s.add_argument("--cases", default=CASES, help="the cases directory (default: conformance/cases)")
    s.add_argument("--theme", action="append", help="run only this theme (repeatable)")
    s.add_argument("--verbose", action="store_true", help="a line per case, not only per failure")


def _report(results: List[Result], verbose: bool) -> None:
    for r in results:
        if verbose or r.status == "FAIL":
            print("%s  %s%s" % (r.status, r.case, "  (%s)" % r.note if r.note and r.status != "FAIL" else ""))
        if r.status == "FAIL":
            _print_fail(r)


def _is_sqlite(target: str) -> bool:
    from .store import is_sqlite
    return is_sqlite(target)


def run(a) -> int:
    base_url = getattr(a, "base_url", None)
    verbose = getattr(a, "verbose", False)
    try:
        themes = load_cases(a.cases, a.theme)
        if base_url:
            if a.target or a.compare or getattr(a, "engines", None) or a.revision or getattr(a, "db", None):
                raise SetupError("--base-url runs against that host: --target, --compare, --engines, --revision and "
                                 "--db are for a host this runner makes")
            if not (a.tokens and a.revision_url):
                raise SetupError("--base-url needs --tokens FILE and --revision-url URL")
            target = Http(url=base_url)
            r = remote_run(target, a.tokens, a.revision_url)
            t0 = time.time()
            results = run_cases(target, themes, r)
            _report(results, verbose)
            return summary(results, "%s (remote)" % base_url, {"remote": time.time() - t0})
        if a.tokens or a.revision_url:
            raise SetupError("--tokens and --revision-url are for --base-url")
        if a.compare and a.target:
            raise SetupError("--compare runs every local target: leave out --target")
        engines = getattr(a, "engines", None) or os.environ.get("PROVENSTREAM_ENGINES") or None
        db = getattr(a, "db", None)
        fx = Fixture(engines, a.revision, db=db)
        # the in-process host's log (the incidents the broken engine's cases bring about, as expected) goes to a file
        # of the run, as a served host's goes to its log, rather than between the results
        logger, handler = logging.getLogger("provenstream"), logging.FileHandler(os.path.join(fx.tmp, "host.log"))
        logger.addHandler(handler)
        logger.propagate = False
        store = "postgres" if db and not _is_sqlite(db) else "sqlite"
        try:
            print("conform: commit %s, proofs %s, on %s" % (fx.commit, " ".join(p for p in PROOFS
                                                                              if p in fx.revisions), store),
                  flush=True)
            names = list(LOCAL_TARGETS) if a.compare else [a.target or "inprocess"]
            per: Dict[str, List[Result]] = {}
            times: Dict[str, float] = {}
            failed: Dict[str, BaseException] = {}

            def one(name: str) -> None:
                t0_ = time.time()
                try:
                    target = LOCAL_TARGETS[name](fx)
                    try:
                        per[name] = run_cases(target, themes, local_run(fx))
                    finally:
                        target.close()
                except BaseException as x:                       # a setup error on one carrier fails the run
                    failed[name] = x
                times[name] = time.time() - t0_

            t0 = time.time()
            threads = [threading.Thread(target=one, args=(n,), name="conform-" + n) for n in names]
            for t in threads:
                t.start()
            for t in threads:
                t.join()
            if failed:
                name, x = next(iter(failed.items()))
                if isinstance(x, (SetupError, CaseError)):
                    raise x
                raise SetupError("%s: %s: %s" % (name, type(x).__name__, x))
            if not a.compare:
                _report(per[names[0]], verbose)
                return summary(per[names[0]], "%s, on %s" % (names[0], store), times)
            for name in names:
                print("conform: %s: %d cases run, %d failed" % (name, len(per[name]),
                                                                 sum(r.status == "FAIL" for r in per[name])))
            results = compare(per)
            _report(results, verbose)
            times["the three, in parallel"] = time.time() - t0
            return summary(results, " = ".join(LOCAL_TARGETS) + " (compared, run in parallel), on " + store, times)
        finally:
            logger.removeHandler(handler)
            logger.propagate = True
            handler.close()
            fx.close()
    except (SetupError, CaseError) as x:
        print("provenstream conform: %s" % x, file=sys.stderr)
        return 2
