# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The stream interface: whether an engine implements it (`check`).

A proof can be valid (it builds, with no `sorry`, and proves its theorems) and its engine pass its own self-test and
describe itself, and still not implement the interface every engine implements (`PROTOCOL.md`): commands in, events
out, judged by the core's rules and then the layer's (`Provenstream.Layer`). A proof built on `Provenstream.Layer`
implements it by construction; the check asks the engine for what that construction gives every layer, on the core's
recorded sessions (`interface/`, copies of `corpus/sessions/core-*`):

- it starts with `{"ready":true}`, speaks engine protocol 2, and describes the core's two commands as the core does:
  the same params, minted ids, fresh count, who, and event, and the core's rules first, in the core's order (a layer's
  guard on a core command is tried after them, so it may only add names after the core's);
- a core refusal stands (`ValidX.base_refusal_stands`): a request the core refuses gets the same refusal (a close by
  someone other than the opener, `only_opener_can_close`, among them);
- an accepted core event is the same event at the same position (the projection, `ValidX.base`), or a refusal by a
  layer's guard, which may only refuse more; after a guard's refusal the stream is the layer's, so the rest of that
  session is not compared;
- a read of a stream holds everything the core's read holds (a layer's state adds keys); a malformed line is malformed;
  a sync or a check of rows the core refuses is refused; a snapshot's and a check's state are the engine's own, not
  compared.

An engine that does not implement it is refused by `provenstream build`, `install` and `check`, and a host refuses a
`stream.open` naming its revision.
"""
from __future__ import annotations
import os
from typing import Any, Dict, List, Optional

from . import wire
from .engine import Engine, EngineFailure

HERE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "interface")
SESSIONS = ("core-rules", "core-cache", "core-malformed")
PROTOCOL = 2                                   # the engine protocol of the interface (`engineProtocol`)


class InterfaceMismatch(Exception):
    """The engine does not implement the stream interface."""


def sessions() -> List[tuple]:
    """Each recorded session: (name, its input lines, the core engine's answers, the ready line first)."""
    out = []
    for name in SESSIONS:
        with open(os.path.join(HERE, name + ".in.jsonl"), encoding="utf-8") as f:
            ins = [l.rstrip("\n") for l in f if l.strip()]
        with open(os.path.join(HERE, name + ".out.jsonl"), encoding="utf-8") as f:
            outs = [wire.loads(l) for l in f if l.strip()]
        out.append((name, ins, outs))
    return out


def base_schema() -> List[dict]:
    """The core's commands as the core describes them: the recorded answer to `{"query":"schema"}`."""
    for name, ins, outs in sessions():
        for line, want in zip(ins, outs[1:]):
            if _parse(line) == {"query": "schema"}:
                return want["commands"]
    raise InterfaceMismatch("the recorded sessions have no schema query")  # never: they are sealed with the corpus


def _parse(line: str) -> Any:
    try:
        return wire.loads(line)
    except wire.BadJson:
        return None


def _holds(want: Any, got: Any) -> bool:
    """`got` holds everything `want` does: every key of an object (a `state` is the engine's own: present is enough)
    and every command of a schema (`_describes`); anything else equal."""
    if isinstance(want, dict) and isinstance(got, dict):
        return all(k in got and (k == "state" or (_has_commands(want[k], got[k]) if k == "commands"
                                                  else _holds(want[k], got[k]))) for k in want)
    return want == got


def _describes(want: Any, got: Any) -> bool:
    """`got` describes the core's command `want` as the core does: every key equal but `rules`, and the core's rules
    first, in order (a layer's guards on the command come after them: they are tried after the core's)."""
    if not (isinstance(want, dict) and isinstance(got, dict)):
        return False
    rest = lambda c: {k: v for k, v in c.items() if k != "rules"}
    rules, theirs = want.get("rules", []), got.get("rules", [])
    return rest(got) == rest(want) and isinstance(theirs, list) and theirs[:len(rules)] == rules


def _has_commands(want: Any, got: Any) -> bool:
    if not (isinstance(want, list) and isinstance(got, list)):
        return False
    named = {c.get("name"): c for c in got if isinstance(c, dict)}
    return all(isinstance(c, dict) and _describes(c, named.get(c.get("name"))) for c in want)


def _refusal(a: Any) -> bool:
    return isinstance(a, dict) and (a.get("accept") is False or a.get("error") == "refused")


def judge(request: Any, want: Any, got: Any) -> str:
    """One line: `same`, `guarded` (a core acceptance a layer's guard refused), or `mismatch`."""
    if isinstance(want, dict) and "error" in want:                       # malformed, or a refused log
        return "same" if isinstance(got, dict) and got.get("error") == want["error"] else "mismatch"
    if isinstance(request, dict) and "command" in request:             # a decision
        if got == want:
            return "same"
        if want.get("accept") is True and _refusal(got) and got.get("stream_id") == want.get("stream_id") \
                and got.get("at") == want.get("at"):
            return "guarded"
        return "mismatch"
    if _holds(want, got):
        return "same"
    return "guarded" if _refusal(got) and not _refusal(want) else "mismatch"


def describe_mismatch(desc: Any) -> Optional[str]:
    """Why an engine's description is not the stream interface's, or None."""
    if not (isinstance(desc, dict) and isinstance(desc.get("schema"), dict)
            and isinstance(desc["schema"].get("commands"), list)):
        return "it does not describe a schema"
    got = {c.get("name"): c for c in desc["schema"]["commands"] if isinstance(c, dict)}
    for c in base_schema():
        if c["name"] not in got:
            return "it does not describe the core's %s (it describes %s)" % (
                c["name"], ", ".join(sorted(map(str, got))) or "no command")
        if not _describes(c, got[c["name"]]):
            return "it describes %s otherwise than the core does" % c["name"]
    p = desc.get("protocol")
    if isinstance(p, bool) or p != PROTOCOL:
        return "it speaks engine protocol %s, not %d" % (wire.dumps(p) if "protocol" in desc else "(none)", PROTOCOL)
    return None


def check(command: List[str], timeout: float = 30.0) -> Dict:
    """Check that the engine `command` starts implements the stream interface, in processes of its own (a host's
    engine never sees the recorded streams). Answers `{"lines", "compared", "guarded": [[session, line]...]}`; raises
    `InterfaceMismatch`, or `EngineFailure` when the engine does not start (which may pass: a host answers it
    `unavailable` and checks again)."""
    report: Dict = {"lines": 0, "compared": 0, "guarded": []}
    for name, ins, outs in sessions():
        eng = Engine(command, timeout=timeout)
        try:
            eng.start()                      # an engine that does not start says nothing of its interface
            if name == SESSIONS[0]:
                try:
                    why = describe_mismatch(eng.query({"query": "describe"}))
                except EngineFailure as x:
                    why = "it does not answer a describe: %s" % x
                if why:
                    raise InterfaceMismatch(why)
            report["lines"] += len(ins)
            for k, (line, want) in enumerate(zip(ins, outs[1:]), 1):
                try:
                    got = eng.line(line.encode("utf-8"))
                except EngineFailure as x:
                    raise InterfaceMismatch("%s line %d: %s" % (name, k, x))
                verdict = judge(_parse(line), want, got)
                if verdict == "mismatch":
                    raise InterfaceMismatch("%s line %d: the core answers %s, this engine %s" % (
                        name, k, wire.dumps(want)[:300], wire.dumps(got)[:300] if got is not None else "nothing"))
                report["compared"] += 1
                if verdict == "guarded":                     # the stream is the layer's now: the rest is not compared
                    report["guarded"].append([name, k])
                    break
        finally:
            eng.stop()
    return report


def check_engine(path: str, timeout: float = 30.0) -> Dict:
    """`check` of a built engine (`build`, `install`, `check`), where an engine that does not start is a failure too."""
    try:
        return check([os.path.abspath(path)], timeout)
    except EngineFailure as x:
        raise InterfaceMismatch("it does not start as an engine: %s" % x)


def summary(report: Dict) -> str:
    s = "interface: the core's sessions, %d of %d lines as the core answers them" % (
        report["compared"], report["lines"])
    if report["guarded"]:
        s += "; a guard refused at %s (the rest of that session not compared)" % ", ".join(
            "%s line %d" % (n, k) for n, k in report["guarded"])
    return s


if __name__ == "__main__":
    import sys
    try:
        print(summary(check(sys.argv[1:])))
    except InterfaceMismatch as x:
        print("interface: MISMATCH: %s" % x, file=sys.stderr)
        sys.exit(1)
