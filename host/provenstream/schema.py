# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""What an engine says of its commands (`{"query":"describe"}`), as the host reads it.

The host has no per-layer code: everything it needs to build a request comes from here: which commands a stream's proof
has, their params and each param's kind, how many fresh ids each takes (its minted fields), which field names the
stream, and, for people and agents (`provenstream -h --proof`), who may send it, its event and that event's fields, and
the names of the rules that can refuse it, in the order they are tried. The engine prints the very schema it decodes
with (`requestFromJ_schema`, `requestToJ_schema` in Service.lean).

An engine's description says the engine protocol it speaks (`"protocol"`). This host reads protocol 2 only: an engine
of any other protocol (or of none) is refused, since what its requests and events look like is not what this host
builds and reads.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Any, Dict, Optional, Tuple


ENGINE_PROTOCOL = 2             # the engine protocol this host reads (`engineProtocol`)
ENGINE_PROTOCOLS = (ENGINE_PROTOCOL,)


class SchemaError(ValueError):
    pass


def protocol_of(describe: Any) -> int:
    """The engine protocol of a description, which must be the one this host reads."""
    p = describe.get("protocol") if isinstance(describe, dict) else None
    if isinstance(p, bool) or p != ENGINE_PROTOCOL:
        raise SchemaError("the engine speaks protocol %s; this host reads protocol %d" % (
            "(none)" if p is None else repr(p), ENGINE_PROTOCOL))
    return p


@dataclass(frozen=True)
class CommandSpec:
    name: str
    params: Tuple[Tuple[str, str], ...]          # (param, kind), in order
    minted: Tuple[str, ...]                      # event fields minted from fresh ids, in order
    stream: str                                  # the field (or minted field) naming the stream
    who: Optional[str] = None                    # who may send it, a sentence (the rules decide)
    event: str = ""                              # its event's name
    event_fields: Tuple[str, ...] = ()           # its event's keys, in order
    rules: Tuple[str, ...] = ()                  # the rules that can refuse it, in the order they are tried

    @property
    def fresh(self) -> int:
        return len(self.minted)

    @property
    def field_names(self) -> Tuple[str, ...]:
        return tuple(f for f, _ in self.params)

    def kind(self, param: str) -> Optional[str]:
        return dict(self.params).get(param)


def _strs(x: Any, what: str) -> Tuple[str, ...]:
    if not isinstance(x, list) or not all(isinstance(s, str) for s in x):
        raise SchemaError("%s: expected a list of strings" % what)
    return tuple(x)


def commands_of(describe: Any) -> Dict[str, CommandSpec]:
    """The command table of an engine's description; refuses a description that is not one, or of an engine
    protocol this host does not read."""
    protocol_of(describe)
    try:
        cmds = describe["schema"]["commands"]
    except (TypeError, KeyError):
        raise SchemaError("not a description: %r" % (describe,))
    if not isinstance(cmds, list):
        raise SchemaError("schema.commands: expected a list")
    out: Dict[str, CommandSpec] = {}
    for c in cmds:
        if not isinstance(c, dict) or not isinstance(c.get("name"), str):
            raise SchemaError("a command without a name: %r" % (c,))
        params = []
        for f in c.get("params", []):
            if not (isinstance(f, dict) and isinstance(f.get("name"), str) and isinstance(f.get("kind"), str)):
                raise SchemaError("%s: a param is not {name, kind}" % c["name"])
            params.append((f["name"], f["kind"]))
        minted = _strs(c.get("minted", []), c["name"] + ".minted")
        if c.get("fresh") != len(minted):
            raise SchemaError("%s: fresh is not the number of minted fields" % c["name"])
        if not isinstance(c.get("stream_id"), str):
            raise SchemaError("%s: stream_id: expected a field name" % c["name"])
        who = c.get("who")
        if who is not None and not isinstance(who, str):
            raise SchemaError("%s: who: expected a sentence" % c["name"])
        ev = c.get("event")
        if not (isinstance(ev, dict) and isinstance(ev.get("name"), str)):
            raise SchemaError("%s: event: expected {name, fields}" % c["name"])
        spec = CommandSpec(c["name"], tuple(params), minted, c["stream_id"], who, ev["name"],
                           _strs(ev.get("fields", []), c["name"] + ".event.fields"),
                           _strs(c.get("rules", []), c["name"] + ".rules"))
        if spec.stream not in spec.minted and spec.stream not in spec.field_names:
            raise SchemaError("%s: the stream field %s is neither minted nor a field" % (spec.name, spec.stream))
        if spec.name in out:
            raise SchemaError("%s: described twice" % spec.name)
        out[spec.name] = spec
    if "stream.open" not in out:
        raise SchemaError("the description has no stream.open: not an engine of a provenstream proof")
    return out
