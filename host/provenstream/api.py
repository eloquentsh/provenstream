# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The HTTP carrier: JSON-RPC 2.0 on POST /rpc, and GET /healthz.

A carrier moves bytes and decides nothing (the methods, the rules and the errors are `host.py`'s and `protocol.py`'s).
POST /rpc reads the body, refusing one over `protocol.MAX_BODY` (`protocol.too_long`) before reading further, turns the
`Authorization: Bearer <token>` header into `Token` (no header is `Token(None)`, which the host answers
`unauthorized`), hands both to `Host.handle` on a worker thread, and writes the answer as the JSON-RPC response, always
with HTTP 200: the outcome is in the body.

GET /healthz is `{"ok": true}` while the store answers, else 503 `{"ok": false}`: status only, no counts and no error
text, since anyone can ask it. The failure itself is logged.
"""
from __future__ import annotations
from typing import Optional

from starlette.applications import Starlette
from starlette.concurrency import run_in_threadpool
from starlette.requests import Request
from starlette.responses import JSONResponse, Response
from starlette.routing import Route

from . import protocol
from .host import Host, Token


def bearer(headers) -> Optional[str]:
    auth = headers.get("authorization", "")
    return auth[len("Bearer "):].strip() if auth.startswith("Bearer ") else None


def _send(answer: protocol.Answer) -> Response:
    return Response(answer.dumps(), media_type="application/json")


def make_app(host: Host) -> Starlette:

    async def rpc(request: Request) -> Response:
        body = b""
        async for chunk in request.stream():
            body += chunk
            if len(body) > protocol.MAX_BODY:
                return _send(protocol.too_long())
        return _send(await run_in_threadpool(host.handle, body, Token(bearer(request.headers))))

    async def healthz(request: Request) -> Response:
        if await run_in_threadpool(host.healthy):
            return JSONResponse({"ok": True})
        return JSONResponse({"ok": False}, status_code=503)

    return Starlette(routes=[Route("/rpc", rpc, methods=["POST"]), Route("/healthz", healthz, methods=["GET"])])
