# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The command line as a client of a Provenstream host, over JSON-RPC (`api.py`): `Remote`, the remote mode's carrier.

Both modes are one object with one method, `handle(method, params)`: the result, or `ClientError` with the exit code of
the answer's kind. `Remote` sends the request over HTTP; `mode.Local` hands it to `Host.handle` in process. Every
subcommand calls `handle`, so it has one code path and the mode only picks the carrier.

The host: `--base-url`, else `PROVENSTREAM_BASE_URL`, else the configured `default_host` (`config.py`), else
`DEFAULT_BASE_URL`. The token: `--token-file`, else `PROVENSTREAM_TOKEN`, else the one stored for that host by
`provenstream login` (`auth.py`), else (discouraged: visible in process lists) `--token`. A token is never printed, and
`Remote` never follows a redirect: urllib would resend the Authorization header to wherever it points.

Exit codes, one per kind of answer (3 to 6 are the answer table's, `protocol.ANSWERS`, the same for a remote host and
for local mode; 7 and 8 are the command line's own):

| code | meaning |
|---|---|
| 0 | done |
| 3 | unauthorized: no token, or the host does not know it |
| 4 | refused by a rule of the proof or of the host: `refused: <rule>`, the rule broken |
| 5 | method not found or invalid params (the host's answer, or the command line's own check against the proof's description), or an invalid request |
| 6 | unavailable: the host could not be reached, or stored nothing and asks for a retry; or no description of a proof to be had |
| 7 | the command needs local mode (a database), and the mode is remote |
| 8 | the mode is misconfigured: an invalid `PROVENSTREAM_MODE`, or settings of the two modes mixed (`mode.py`) |
"""
from __future__ import annotations
import json, os, re, sys, urllib.error, urllib.request
from typing import Any, Dict, Optional

from . import __version__, protocol, wire

# The default host: the local host, where `provenstream serve` listens with no flags (127.0.0.1, port 8080). A remote
# host is named with --base-url, PROVENSTREAM_BASE_URL or the configured default_host.
DEFAULT_BASE_URL = "http://127.0.0.1:8080"

_exit = lambda code: protocol.ANSWERS[code].exit
EXIT_UNAUTHORIZED, EXIT_REFUSED = _exit("unauthorized"), _exit("refused")
EXIT_PARAMS, EXIT_UNAVAILABLE = _exit("invalid_params"), _exit("unavailable")
EXIT_NEEDS_LOCAL, EXIT_MODE = 7, 8


class ClientError(Exception):
    def __init__(self, exit_code: int, message: str):
        self.exit_code, self.message = exit_code, message
        super().__init__(message)


def base_url(flag: Optional[str]) -> str:
    return (flag or os.environ.get("PROVENSTREAM_BASE_URL") or DEFAULT_BASE_URL).rstrip("/")


def token(token_file: Optional[str], flag: Optional[str]) -> str:
    if token_file:
        try:
            with open(token_file, encoding="utf-8") as f:
                t = f.read().strip()
        except OSError as x:
            raise ClientError(EXIT_UNAUTHORIZED, "unauthorized: cannot read the token file: %s" % x.strerror)
        if not t:
            raise ClientError(EXIT_UNAUTHORIZED, "unauthorized: the token file is empty")
        return t
    t = os.environ.get("PROVENSTREAM_TOKEN")
    if t:
        return t.strip()
    if flag:
        print("provenstream: warning: --token is visible in process lists; prefer PROVENSTREAM_TOKEN or --token-file",
              file=sys.stderr)
        return flag
    raise ClientError(EXIT_UNAUTHORIZED, "unauthorized: no token (set PROVENSTREAM_TOKEN or pass --token-file)")


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None                     # the 3xx is answered as an HTTPError: unavailable, the token sent nowhere else


_OPENER = urllib.request.build_opener(_NoRedirect)


class Remote:
    """Remote mode: each call one JSON-RPC request to the host at `url`, as the principal of `tok`."""

    def __init__(self, url: str, tok: str, timeout: float = 60.0):
        self.url, self.tok, self.timeout = url, tok, timeout

    def handle(self, method: str, params: Optional[Dict[str, Any]] = None) -> Any:
        """One call; answers its result or raises `ClientError` with the exit code of its kind."""
        body = wire.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params or {}}).encode("utf-8")
        req = urllib.request.Request(self.url + "/rpc", body, {"Content-Type": "application/json",
                                                               "Authorization": "Bearer " + self.tok,
                                                               "User-Agent": "provenstream/%s" % __version__})
        try:
            with _OPENER.open(req, timeout=self.timeout) as f:
                ans = wire.loads(f.read())
        except urllib.error.HTTPError as x:
            raise ClientError(EXIT_UNAVAILABLE, "unavailable: the host answered HTTP %d" % x.code)
        except (urllib.error.URLError, OSError) as x:
            raise ClientError(EXIT_UNAVAILABLE, "unavailable: cannot reach %s: %s" % (self.url, getattr(x, "reason", x)))
        except wire.BadJson:
            raise ClientError(EXIT_UNAVAILABLE, "unavailable: the host's answer is not JSON")
        if not isinstance(ans, dict):
            raise ClientError(EXIT_UNAVAILABLE, "unavailable: the host's answer is not JSON-RPC")
        if "error" in ans:
            e = ans["error"] if isinstance(ans["error"], dict) else {}
            raise error_of(e.get("code"), e.get("message", "?"), e.get("data") or {})
        return ans.get("result")

    def close(self) -> None:
        pass

    def __enter__(self) -> "Remote":
        return self

    def __exit__(self, *exc: Any) -> None:
        self.close()


def error_of(code: Any, message: str, data: Dict[str, Any]) -> "ClientError":
    """The `ClientError` of a JSON-RPC error, the same for a remote host and for local mode: its kind is `data.code`,
    or for a host from before `data.code` the JSON-RPC code, and its exit code is the answer table's."""
    kind = protocol.code_of(code, data)
    exit_code = protocol.ANSWERS[kind].exit
    if kind == "unauthorized":
        return ClientError(exit_code, "unauthorized: %s" % (data.get("detail") or "the host does not accept this token"))
    if kind == "refused":
        return ClientError(exit_code, "refused: %s%s" % (data.get("reason", "?"), ": " + data["detail"]
                                                         if data.get("detail") else ""))
    if kind == "method_not_found":
        return ClientError(exit_code, "method not found%s" % (": " + data["detail"] if data.get("detail") else ""))
    if kind != "unavailable":
        return ClientError(exit_code, "invalid params: %s" % (data.get("detail") or message))
    if data.get("incident"):
        return ClientError(exit_code, "unavailable: nothing stored; retry (incident %s)" % data["incident"])
    return ClientError(exit_code, "unavailable: %s" % (data.get("detail") or message))


def pick(result: Any, path: str) -> Any:
    """The value at a dotted `path` of `result` (`events.0.seq`; a list index may be negative), or invalid params."""
    cur = result
    for i, part in enumerate(path.split(".")):
        if isinstance(cur, list) and re.fullmatch(r"-?[0-9]+", part) and -len(cur) <= int(part) < len(cur):
            cur = cur[int(part)]
        elif isinstance(cur, dict) and part in cur:
            cur = cur[part]
        else:
            have = ("keys: " + ", ".join(sorted(cur)) if isinstance(cur, dict) else
                    "indexes 0 to %d" % (len(cur) - 1) if isinstance(cur, list) and cur else "nothing below it")
            raise ClientError(EXIT_PARAMS, "invalid params: --field %s: the result has no %s (%s has %s)"
                              % (path, ".".join(path.split(".")[:i + 1]),
                                 ".".join(path.split(".")[:i]) or "the result", have))
    return cur


def show(result: Any, field: Optional[str] = None) -> None:
    """A result as indented JSON, or with `field` (-q) the value at that path alone: a string as it is, anything
    else as JSON. A path the result does not have still exits 5, but the call itself succeeded (a write is stored), so
    the whole result is printed first and the message says so: nothing the host answered is lost to a typo."""
    if field is None:
        print(json.dumps(result, indent=2, ensure_ascii=False, sort_keys=True))
        return
    try:
        v = pick(result, field)
    except ClientError as x:
        print(json.dumps(result, indent=2, ensure_ascii=False, sort_keys=True))
        raise ClientError(x.exit_code, "the call succeeded (its whole result is printed above), but " + x.message)
    print(v if isinstance(v, str) else json.dumps(v, ensure_ascii=False, sort_keys=True))
