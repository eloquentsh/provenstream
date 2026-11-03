# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""JSON as the host reads it from callers and writes it to the engine (why: Provenstream/Engine/Json.lean).

- a body with a repeated key is refused;
- `NaN`, `Infinity` and numbers that overflow are refused (not JSON);
- a string holding a lone UTF-16 surrogate is refused (it has no UTF-8 encoding);
- the engine is sent UTF-8 unescaped (`ensure_ascii=False`).
"""
from __future__ import annotations
import json
from typing import Any, List, Tuple


class BadJson(ValueError):
    pass


def _pairs(pairs: List[Tuple[str, Any]]) -> dict:
    out: dict = {}
    for k, v in pairs:
        if k in out:
            raise BadJson("repeated key: %r" % k)
        out[k] = v
    return out


def _constant(name: str) -> Any:
    raise BadJson("not JSON: " + name)


def _float(s: str) -> float:
    x = float(s)
    if x in (float("inf"), float("-inf")):
        raise BadJson("number out of range: " + s)
    return x


def _check_strings(x: Any) -> None:
    if isinstance(x, str):
        try:
            x.encode("utf-8")
        except UnicodeEncodeError:
            raise BadJson("a string holds a lone UTF-16 surrogate") from None
    elif isinstance(x, dict):
        for k, v in x.items():
            _check_strings(k)
            _check_strings(v)
    elif isinstance(x, list):
        for v in x:
            _check_strings(v)


def loads(text: Any) -> Any:
    """Strict JSON: no repeated keys, no NaN or Infinity, no lone surrogates."""
    try:
        if isinstance(text, (bytes, bytearray)):
            text = bytes(text).decode("utf-8")
        value = json.loads(text, object_pairs_hook=_pairs, parse_constant=_constant, parse_float=_float)
    except BadJson:
        raise
    except (ValueError, RecursionError) as x:
        raise BadJson(str(x)) from None
    try:
        _check_strings(value)
    except RecursionError:
        raise BadJson("nested too deeply") from None
    return value


def dumps(value: Any) -> str:
    """One line of compact JSON, UTF-8 unescaped (see above)."""
    return json.dumps(value, ensure_ascii=False, separators=(",", ":"), allow_nan=False)
