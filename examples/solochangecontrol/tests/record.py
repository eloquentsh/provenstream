# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Sequences the state machine ran, written as conformance cases (conformance/README.md, make_cases.py): one case per
request, by a role, with the answer the host must give; the stream read back at the end.

A trace is the machine's list of steps `{"request", "answer", "want", "probe"}`. Not everything an engine is asked can
be asked of a host, so a step is left out when a host could never send it: a wrong number of fresh ids, an open of a
stream that exists (the host mints every id), a request malformed in its `actor_id` or `fresh`, and the acceptance
probes (snapshot, merge, load) unless the probe is the step that failed. A trace with more than four principals has
no roles to run under and is refused (`Unrepresentable`).

    python3 record.py TRACE.json [NAME]     print the cases of a saved trace
"""
from __future__ import annotations
import json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import solo_model as M  # noqa: E402

PROOF = "solochangecontrol"
ROLES = ("opener", "other", "third", "outsider")
NOWHERE = "00000000-0000-4000-8000-000000000000"      # a stream no host has: never opened
TABLE = {"invalid_params": (-32602, "invalid params"), "refused": (-32002, "refused")}


class Unrepresentable(Exception):
    """The trace cannot be a host's session: more than four principals."""


def _err(code, **data):
    rpc, message = TABLE[code]
    return {"error": {"code": rpc, "message": message, "data": dict({"code": code}, **data)}}


def _hostable(step: dict, last: bool) -> bool:
    want, req = step["want"], step["request"]
    if step.get("probe") and not (last and step.get("failed")):
        return False
    if want in ("fresh_ids_must_match_the_command", "stream_id_must_be_new"):
        return False
    if want == "malformed":
        cmd = req["command"]
        # the host fills actor_id in and mints fresh: only a command malformed in its own params is sendable
        return M.valid_uuid(req["actor_id"]) and all(M.valid_uuid(x) for x in req["fresh"]) and \
            isinstance(cmd, dict) and cmd.get("command") in M.SCHEMA
    return True


def cases_of(trace: list, name: str) -> list:
    """The conformance cases of a trace, ids `<name>/<nn>-<command>`; the streams read back at the end."""
    steps = [s for i, s in enumerate(trace) if _hostable(s, i == len(trace) - 1)]
    roles, streams, model = {}, {}, M.Model()
    out, n = [], 0

    def role(p):
        if p not in roles:
            if len(roles) == len(ROLES):
                raise Unrepresentable("more than %d principals" % len(ROLES))
            roles[p] = "$" + ROLES[len(roles)]
        return roles[p]

    tag = name.replace("-", "_")      # bindings are per run of the theme, so each sequence names its own

    def sid(x):
        return "$" + streams[x] if x in streams else NOWHERE

    def chain(x, at):
        return "%s_c%d" % (streams[x], at)

    def add(who, method, params, expect, label):
        nonlocal n
        n += 1
        out.append({"id": "%s/%02d-%s" % (name, n, label), "who": who[1:], "method": method, "params": params,
                    "expect": expect, "proof": PROOF})

    for step in steps:
        req = step["request"]
        actor, cmd = req["actor_id"], dict(req["command"])
        method = cmd.pop("command")
        who = role(actor)
        params = {}
        for k, v in cmd.items():
            if k == "stream_id":
                params[k] = sid(v) if M.valid_uuid(v) else v
            elif k == "developer_id" and M.valid_uuid(v):
                params[k] = role(v)
            elif k == "proof_revision_url" and v == M.PROOF_URL:
                params[k] = "$url_" + PROOF
            else:
                params[k] = v
        want = step["want"]
        if want == "malformed":
            # the host finds the stream before it asks the engine to decode: a malformed command on a stream the host
            # does not have is refused for the stream, not for its params
            s0 = cmd.get("stream_id")
            if method != "stream.open" and M.valid_uuid(s0) and not model.stream(s0).opened:
                add(who, method, params, _err("refused", reason="stream_must_exist"), method)
            else:
                add(who, method, params, _err("invalid_params", detail="$string"), method)
            continue
        want2, s, at, ev = model.step(req)
        assert want2 == want, (want2, want, req)
        if want is not None:
            add(who, method, params, _err("refused", reason=want), method)
            continue
        if method == "stream.open":
            streams[s] = "%s_s%d" % (tag, len(streams) + 1)
            params.pop("stream_id", None)
        e = dict(ev)
        e["stream_id"] = "$uuid:" + streams[s] if method == "stream.open" else "$" + streams[s]
        e["actor_id"] = role(e["actor_id"])
        if "developer_id" in e:
            e["developer_id"] = role(e["developer_id"])
        if e.get("proof_revision_url") == M.PROOF_URL:
            e["proof_revision_url"] = "$url_" + PROOF
        add(who, method, params, {"result": {"seq": at, "event": e, "chain": "$hex64:" + chain(s, at)}}, method)
    for s, bound in streams.items():
        stream = model.streams[s]
        evs = []
        for i, ev in enumerate(stream.events):
            e = dict(ev, seq=i, chain="$" + chain(s, i))
            e["stream_id"] = "$" + bound
            e["actor_id"] = roles[e["actor_id"]]
            if "developer_id" in e:
                e["developer_id"] = roles[e["developer_id"]]
            if e.get("proof_revision_url") == M.PROOF_URL:
                e["proof_revision_url"] = "$url_" + PROOF
            evs.append(e)
        view = stream.read()
        view["stream_id"], view["opener_id"] = "$" + bound, roles[view["opener_id"]]
        if view["proof_revision_url"] == M.PROOF_URL:
            view["proof_revision_url"] = "$url_" + PROOF
        view["developers"] = [{"change_id": d["change_id"], "developer_id": roles[d["developer_id"]]}
                              for d in view["developers"]]
        view["reviewers"] = [{"change_id": r["change_id"], "reviewer_id": roles[r["reviewer_id"]]}
                             for r in view["reviewers"]]
        reader = "$opener"
        add(reader, "stream.events", {"stream_id": "$" + bound},
            {"result": {"stream_id": "$" + bound, "events": evs, "next": None}}, "events")
        add(reader, "stream.head", {"stream_id": "$" + bound},
            {"result": {"stream_id": "$" + bound, "length": len(evs), "chain": "$" + chain(s, len(evs) - 1)}}, "head")
        add(reader, "stream.get", {"stream_id": "$" + bound}, {"result": view}, "view")
        rows = [{"seq": i, "request": "$any", "event": "$any", "meta_salt": "$any", "chain": "$" + chain(s, i)}
                for i in range(len(evs))]
        add(reader, "stream.rows", {"stream_id": "$" + bound},
            {"result": {"stream_id": "$" + bound, "rows": rows, "next": None}}, "rows")
        out[-1]["check"] = "chain"
    return out


def line(x) -> str:
    return json.dumps(x, ensure_ascii=False, separators=(",", ":"))


def write_theme(sequences: list, path: str, theme: str = PROOF) -> int:
    """Write `cases/<theme>.jsonl`: `sequences` is a list of (name, trace). Answers the number of cases."""
    cases = []
    for name, trace in sequences:
        cases.extend(cases_of(trace, name))
    ids = [c["id"] for c in cases]
    assert len(set(ids)) == len(ids), "repeated case ids"
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        for c in cases:
            f.write(line(dict(c, id="%s/%s" % (theme, c["id"]))) + "\n")
    return len(cases)


def dump_failing(trace: list, why, directory: str) -> str:
    """Write a failing trace twice: raw (`failing.trace.json`, with the engine's answers and what the model wanted) and,
    when a host could run it, as cases (`failing.jsonl`, the last case expecting what the model wanted). Overwritten
    on every failure, so after Hypothesis shrinks the files hold the smallest sequence found."""
    os.makedirs(directory, exist_ok=True)
    raw = os.path.join(directory, "failing.trace.json")
    with open(raw, "w", encoding="utf-8") as f:
        json.dump({"why": [str(x) for x in why] if isinstance(why, (list, tuple)) else str(why), "steps": trace}, f,
                  indent=1, ensure_ascii=False, default=str)
    path = os.path.join(directory, "failing.jsonl")
    try:
        cases = cases_of(trace, "failing")
    except (Unrepresentable, AssertionError, KeyError, TypeError) as x:
        with open(path, "w", encoding="utf-8") as f:
            f.write(line({"id": "failing/unrepresentable", "note": "no host could run this trace: %s" % x}) + "\n")
        return raw
    with open(path, "w", encoding="utf-8") as f:
        for c in cases:
            f.write(line(dict(c, id="%s/%s" % (PROOF, c["id"]))) + "\n")
    return raw


def describe(trace: list) -> str:
    """The sequence as people read it: one line per step, `actor command fields -> answer`."""
    out = []
    for step in trace:
        if step.get("probe") and not step.get("failed"):
            continue
        req, cmd = step["request"], dict(step["request"]["command"])
        name = cmd.pop("command")
        fields = " ".join("%s=%s" % (k, _short(v)) for k, v in cmd.items())
        got = step["answer"]
        answer = got.get("error") or ("accepted" if got.get("accept") else got.get("reason"))
        want = "accepted" if step["want"] is None else step["want"]
        mark = "" if answer == want else "   <-- the model wanted %s" % want
        out.append("%s %s %s -> %s%s" % (_short(req["actor_id"]), name, fields, answer, mark))
    return "\n".join(out)


def _short(v) -> str:
    if isinstance(v, str) and M.valid_uuid(v):
        return v[:8]
    if isinstance(v, str) and v.startswith("https://example.org/repo/commit/"):
        return v.rsplit("/", 1)[1]
    return json.dumps(v, ensure_ascii=False) if not isinstance(v, str) else v


if __name__ == "__main__":
    with open(sys.argv[1], encoding="utf-8") as f:
        data = json.load(f)
    steps = data["steps"] if isinstance(data, dict) else data
    for c in cases_of(steps, sys.argv[2] if len(sys.argv) > 2 else "trace"):
        print(line(c))
