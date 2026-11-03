# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The per-stream hash chain, and the salted commitment to `meta`. This docstring is the specification.

Computed by the host, not proved (gap_host_chain, docs/tcb.md). The engine and the proofs do not see it.

Commitment
    Each accepted row gets a fresh 16-byte random salt. If the row's command has a `meta` string, its commitment is

        "sha256:" + hex(SHA-256(salt || UTF-8(meta)))

    A row without meta (absent or null) still has a salt, so all rows look alike, and is hashed unchanged.

Redaction
    R is the stored request with `command.meta` replaced by the commitment, E the stored event with `meta` replaced by
    the same commitment, each serialised with `wire.dumps` (compact JSON, UTF-8, keys in their stored order): the same
    canonical form the store writes. Without meta, R and E are the stored request and event as they are.

Chain
    h_genesis = SHA-256("provenstream-chain-v1" || 0x00 || UTF-8(stream id))
    h_n       = SHA-256(h_{n-1} || u64be(n) || u32be(len R) || R || u32be(len E) || E)

    for the row at sequence number n (0-based), u64be and u32be big-endian unsigned integers of 8 and 4 bytes. The head
    of a stream after row n is h_n; a receipt is that head, in hex.

Legacy rows
    Rows written before the chain existed carry no salt and no chain. Their contribution is computed with an empty salt
    and never stored (events are append-only); the chain continues from the computed head.

Erased meta
    A row whose meta was removed from storage carries its commitment instead (`meta_commitment` in a rows file), and
    `null` in place of the meta in its request and event (the key keeps its position, so the canonical form is the
    same). Its R and E are rebuilt with that commitment, so the chain still verifies; its content can no longer be
    checked, and an engine cannot replay it (its event no longer is what the engine gives).
"""
from __future__ import annotations
import hashlib, hmac, secrets, struct
from dataclasses import dataclass
from typing import Any, Dict, Iterable, List, Optional, Tuple

from . import wire

TAG = b"provenstream-chain-v1"
SALT_BYTES = 16


def new_salt() -> bytes:
    return secrets.token_bytes(SALT_BYTES)


def genesis(stream: str) -> bytes:
    return hashlib.sha256(TAG + b"\x00" + stream.encode("utf-8")).digest()


def commitment(salt: bytes, meta: str) -> str:
    return "sha256:" + hashlib.sha256(salt + meta.encode("utf-8")).hexdigest()


def meta_of(request: Dict[str, Any]) -> Optional[str]:
    m = request.get("command", {}).get("meta")
    return m if isinstance(m, str) else None


def redact(request: Dict[str, Any], event: Dict[str, Any], salt: Optional[bytes],
           erased: Optional[str] = None) -> Tuple[bytes, bytes, Optional[str]]:
    """R and E of a row (bytes), and the meta commitment (None without meta). `erased`: the commitment a row carries
    instead of its meta."""
    c = erased
    if c is None:
        m = meta_of(request)
        if m is not None:
            c = commitment(salt or b"", m)
    if c is None:
        return wire.dumps(request).encode("utf-8"), wire.dumps(event).encode("utf-8"), None
    req = dict(request, command=dict(request["command"], meta=c))
    ev = dict(event, meta=c)
    return wire.dumps(req).encode("utf-8"), wire.dumps(ev).encode("utf-8"), c


def link(prev: bytes, seq: int, r: bytes, e: bytes) -> bytes:
    return hashlib.sha256(prev + struct.pack(">Q", seq) + struct.pack(">I", len(r)) + r +
                          struct.pack(">I", len(e)) + e).digest()


@dataclass
class Row:
    seq: int
    request: Dict[str, Any]
    event: Dict[str, Any]
    salt: Optional[bytes] = None          # None: a legacy row (empty salt)
    chain: Optional[bytes] = None         # the stored head after this row; None: legacy
    erased: Optional[str] = None          # the commitment of an erased meta


def heads(stream: str, rows: Iterable[Row], start: Optional[bytes] = None) -> List[bytes]:
    """The head after each row, computed from the rows (stored heads are not trusted)."""
    h = start or genesis(stream)
    out = []
    for row in rows:
        r, e, _ = redact(row.request, row.event, row.salt, row.erased)
        h = link(h, row.seq, r, e)
        out.append(h)
    return out


@dataclass
class Report:
    ok: bool
    detail: str
    head: Optional[bytes]
    erased: List[int]


def verify(stream: str, rows: List[Row], held: Optional[Dict[int, str]] = None, held_last: Optional[str] = None
           ) -> Report:
    """Recompute every commitment and the chain; refuse at the first mismatch, naming the seq. Rows must be the
    stream's rows from 0, in order, each with its stored head unless legacy. `held`: heads a client kept ({seq: hex});
    `held_last`: the head a client kept as the stream's last."""
    h = genesis(stream)
    erased = []
    for i, row in enumerate(rows):
        if row.seq != i:
            return Report(False, "row %d has seq %d: rows are missing, reordered or repeated" % (i, row.seq), None, erased)
        if row.erased is not None:
            erased.append(row.seq)
        r, e, _ = redact(row.request, row.event, row.salt, row.erased)
        h = link(h, row.seq, r, e)
        if row.chain is not None and not hmac.compare_digest(h, row.chain):
            return Report(False, "seq %d: the stored head is not the hash of the history up to it" % row.seq, None,
                          erased)
        want = (held or {}).get(row.seq)
        if want is not None and h.hex() != want.lower():
            return Report(False, "seq %d: the head is not the one held" % row.seq, None, erased)
    for seq in sorted(held or {}):
        if seq >= len(rows):
            return Report(False, "a head is held for seq %d, but the rows end at seq %d: the stream was truncated"
                          % (seq, len(rows) - 1), None, erased)
    if held_last is not None and (not rows or h.hex() != held_last.lower()):
        return Report(False, "the last head is not the one held (seq %d): the stream was changed or truncated"
                      % (len(rows) - 1), None, erased)
    return Report(True, "%d rows chain to head %s" % (len(rows), h.hex() if rows else genesis(stream).hex()),
                  h if rows else None, erased)


def row_from_json(d: Dict[str, Any]) -> Row:
    """A row as `stream.rows` answers it (request and event as stored JSON text, or as objects; salt and chain hex)."""
    obj = lambda v: wire.loads(v) if isinstance(v, str) else v
    hx = lambda v: bytes.fromhex(v) if isinstance(v, str) and v else None
    return Row(d["seq"], obj(d["request"]), obj(d["event"]), hx(d.get("meta_salt")), hx(d.get("chain")),
               d.get("meta_commitment"))
