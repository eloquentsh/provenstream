# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Minting ids: UUIDv7 (RFC 9562), for streams and principals alike.

An id says nothing about what it names. A repeated stream id is only refused (`stream_id_must_be_new`); these make one
rare: 48 bits of
millisecond time, a 12-bit counter that keeps ids from one process increasing within a millisecond, 62 random bits.
"""
from __future__ import annotations
import re, secrets, threading, time, uuid

CANONICAL_ID = re.compile(r"[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}")

_lock = threading.Lock()
_last_ms = -1
_counter = 0


def uuid7() -> str:
    global _last_ms, _counter
    with _lock:
        ms = time.time_ns() // 1_000_000
        if ms <= _last_ms:
            ms = _last_ms
            _counter += 1
            if _counter > 0xFFF:
                ms += 1
                _counter = 0
        else:
            _counter = secrets.randbits(11)
        _last_ms = ms
        counter = _counter
    rand = secrets.randbits(62)
    value = (ms & ((1 << 48) - 1)) << 80 | 0x7 << 76 | counter << 64 | 0b10 << 62 | rand
    return str(uuid.UUID(int=value))
