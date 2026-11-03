# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The stdio carrier: JSON-RPC 2.0 over stdin and stdout, one request per line (`provenstream serve --stdio`).

The local transport of LSP and MCP, so a program in any language can embed a host by starting a process. A carrier
moves bytes and decides nothing: each line read is handed to `Host.handle` as it is, and the answer written is
`Answer.dumps()`, the very bytes the HTTP carrier sends as its body for the same message and principal, then a
newline. Lines are answered one at a time, in order, each answer flushed before the next line is read, so a caller may
write a request and wait for its line. Logs go to stderr only; stdout carries answers and nothing else.

A session is one principal, fixed at launch: `Operator(principal)` (`--as`, which needs the database, as local mode
does) or `Token(t)` (`--token-file`), which the host looks up on every request as it does a bearer header, so a token
rotated or revoked mid-session stops working mid-session.

Framing. A line ends at `\\n` (a `\\r` before it is dropped). An empty line is no request and gets no answer; every
other line gets exactly one. A line over `protocol.MAX_BODY` bytes is answered `invalid_request` with id null
(`protocol.too_long`, the answer the HTTP carrier and `Host.handle` give a message over it), and the rest of it is read
and dropped without being held, so the session goes on with the next line. A last line without a newline is a request
like any other. End of input ends the session, exit 0, with the store and the engines closed by the caller.
"""
from __future__ import annotations
import logging
from typing import BinaryIO

from . import protocol
from .host import Auth, Host

log = logging.getLogger("provenstream.stdio")

CHUNK = 1 << 16


def serve(host: Host, auth: Auth, stdin: BinaryIO, stdout: BinaryIO, max_line: int = protocol.MAX_BODY) -> int:
    """Answer every line of `stdin` on `stdout` as `auth`, until end of input. Answers the exit code (0)."""
    n = 0
    while True:
        line = stdin.readline(max_line + 2)          # the line, its \r and its \n: anything longer is over-long
        if not line:
            break
        if len(line) == max_line + 2 and not line.endswith(b"\n"):    # cut off: over-long whatever follows
            while line and not line.endswith(b"\n"):                   # drop the rest, a chunk at a time
                line = stdin.readline(CHUNK)
            answer = protocol.too_long(max_line)
        else:
            body = line[:-1] if line.endswith(b"\n") else line
            if body.endswith(b"\r"):
                body = body[:-1]
            if not body:
                continue
            answer = protocol.too_long(max_line) if len(body) > max_line else host.handle(body, auth)
        stdout.write(answer.dumps().encode("utf-8") + b"\n")
        stdout.flush()
        n += 1
    log.info("stdio: end of input after %d requests", n)
    return 0
