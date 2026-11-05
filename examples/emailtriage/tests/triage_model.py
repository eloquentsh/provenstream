# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""A Python restatement of what the emailtriage engine does with one request: the wire's decoding (what is
`malformed`), the core's admission, the layer's fifteen rules in the engine's order, the event an accepted request
becomes, and the notes it leaves. The oracle every test in this directory judges the engine by.

It is written from EmailTriage/Layer.lean and the core, not imported from them, so a difference between the two is a
finding. `RULES` is the layer's list, in its order; `judge` tries them as the engine does and answers the first that
refuses.
"""
from __future__ import annotations
import re

PROOF_URL = "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/emailtriage"

SCHEMA = {
    "stream.open": [("proof_revision_url", "text"), ("meta", "meta")],
    "stream.close": [("stream_id", "uuid"), ("meta", "meta")],
    "triage.create": [("stream_id", "uuid"), ("triage_id", "uuid"), ("message_url", "eml"), ("meta", "meta")],
    "triage.ask": [("stream_id", "uuid"), ("triage_id", "uuid"), ("adviser_id", "uuid"), ("meta", "meta")],
    "triage.advise": [("stream_id", "uuid"), ("triage_id", "uuid"), ("verdict", "verdict"), ("meta", "meta")],
    "triage.review": [("stream_id", "uuid"), ("triage_id", "uuid"), ("verdict", "verdict"), ("meta", "meta")],
    "triage.reply": [("stream_id", "uuid"), ("triage_id", "uuid"), ("email_id", "uuid"), ("meta", "meta")],
    "triage.ignore": [("stream_id", "uuid"), ("triage_id", "uuid"), ("meta", "meta")],
}
EVENT_OF = {"stream.open": "stream.opened", "stream.close": "stream.closed", "triage.create": "triage.created",
            "triage.ask": "triage.asked", "triage.advise": "triage.advised", "triage.review": "triage.reviewed",
            "triage.reply": "triage.replied", "triage.ignore": "triage.ignored"}
FRESH = {"stream.open": 1}
LAYER = tuple(c for c in SCHEMA if c.startswith("triage."))
CORE = ("stream.open", "stream.close")
COMMANDS = CORE + LAYER
VERDICTS = ("reply", "ignore")

HEX = re.compile(r"[0-9a-f]*\Z")


def valid_uuid(s) -> bool:
    if not isinstance(s, str):
        return False
    parts = s.split("-")
    return len(parts) == 5 and [len(p) for p in parts] == [8, 4, 4, 4, 12] and all(HEX.match(p) for p in parts)


def no_control(s: str) -> bool:
    return all(32 <= ord(c) and ord(c) != 127 for c in s)


def valid_meta(m) -> bool:
    return m is None or (isinstance(m, str) and "\x00" not in m and len(m.encode("utf-8")) <= 4096 and no_control(m))


def valid_url(s) -> bool:
    if not isinstance(s, str) or len(s) > 2048 or not all(32 < ord(c) and ord(c) != 127 for c in s):
        return False
    parts = s.split("://")
    return len(parts) == 2 and bool(parts[0]) and bool(parts[1])


def valid_eml(s) -> bool:
    return valid_url(s) and s.endswith(".eml")


def valid_verdict(s) -> bool:
    return isinstance(s, str) and s in VERDICTS


def _alnum(c: str) -> bool:
    return ("a" <= c <= "z") or ("A" <= c <= "Z") or ("0" <= c <= "9")


def valid_revision(s: str) -> bool:
    return len(s) in (40, 64) and bool(HEX.match(s))


def valid_segment(seg: str) -> bool:
    return seg not in ("", ".", "..") and all(_alnum(c) or c in "._-" for c in seg)


def valid_revision_url(s) -> bool:
    if not isinstance(s, str) or len(s) > 2048 or not all(32 < ord(c) and ord(c) != 127 for c in s):
        return False

    def repo_ok(repo: str) -> bool:
        parts = repo.split("://")
        if len(parts) != 2:
            return False
        scheme, rest = parts
        segs = rest.split("/")
        return bool(scheme) and all(_alnum(c) or c in "+-." for c in scheme) and len(segs) >= 2 and all(segs)

    def split(sep: str) -> bool:
        parts = s.split(sep)
        return len(parts) == 2 and repo_ok(parts[0]) and valid_revision(parts[1])

    def tree() -> bool:
        parts = s.split("/tree/")
        if len(parts) != 2:
            return False
        rest = parts[1].split("/")
        return len(rest) >= 2 and repo_ok(parts[0]) and valid_revision(rest[0]) and all(map(valid_segment, rest[1:]))

    return split("/commit/") or split("#") or split("@") or tree()


def well_formed(request: dict) -> bool:
    if set(request) != {"actor_id", "command", "fresh"} or not valid_uuid(request["actor_id"]):
        return False
    if not isinstance(request["fresh"], list) or not all(valid_uuid(x) for x in request["fresh"]):
        return False
    cmd = request["command"]
    if not isinstance(cmd, dict) or cmd.get("command") not in SCHEMA:
        return False
    fields = SCHEMA[cmd["command"]]
    allowed = {"command"} | {n for n, _ in fields}
    if not set(cmd) <= allowed:
        return False
    for name, kind in fields:
        if name not in cmd:
            if kind == "meta" or kind.endswith("?"):
                continue
            return False
        v = cmd[name]
        if kind == "uuid" and not valid_uuid(v):
            return False
        if kind == "eml" and not valid_eml(v):
            return False
        if kind == "verdict" and not valid_verdict(v):
            return False
        if kind == "text" and not (isinstance(v, str) and "\x00" not in v):
            return False
        if kind == "meta" and not valid_meta(v):
            return False
    return True


class Stream:
    def __init__(self, sid: str):
        self.id = sid
        self.opened = False
        self.closed = False
        self.opener = None
        self.url = None
        self.notes = []
        self.events = []

    def noted(self, what, k):
        return any(n[0] == what and n[1] == k for n in self.notes)

    def contains(self, note):
        return note in self.notes

    def decided(self, k):
        return self.noted("replied", k) or self.noted("ignored", k)

    def reviewed(self, k):
        return self.noted("reviewer", k)

    def triages(self):
        return [n[1] for n in self.notes if n[0] == "triage"]

    def advisers(self, k):
        return [n[2] for n in self.notes if n[0] == "adviser" and n[1] == k]

    def advised(self, k):
        return [n[2] for n in self.notes if n[0] == "advice" and n[1] == k]

    def reviewers(self, k):
        return [n[2] for n in self.notes if n[0] == "reviewer" and n[1] == k]

    def undecided(self):
        return [k for k in self.triages() if not self.decided(k)]

    def pairs(self, what, who):
        return [{"triage_id": n[1], who: n[2]} for n in self.notes if n[0] == what]

    def items(self, what):
        return [n[1] for n in self.notes if n[0] == what]

    def read(self):
        if not self.opened:
            return {"error": "stream_must_exist"}
        return {"stream_id": self.id, "proof_revision_url": self.url, "opener_id": self.opener, "closed": self.closed,
                "triages": self.pairs("triage", "message_url"),
                "advisers": self.pairs("adviser", "adviser_id"),
                "advice": self.pairs("advice", "adviser_id"),
                "verdicts": self.pairs("verdict", "verdict"),
                "reviewers": self.pairs("reviewer", "reviewer_id"),
                "calls": self.pairs("call", "verdict"),
                "replied": self.pairs("replied", "email_id"),
                "ignored": self.items("ignored")}


def _k(f):
    return f["triage_id"]


RULES = [
    ("only_opener_can_create", ("triage.create",), lambda s, a, c, f: s.opener == a),
    ("triage_id_must_be_new", ("triage.create",), lambda s, a, c, f: not s.noted("triage", _k(f))),
    ("triage_must_exist", ("triage.ask", "triage.advise", "triage.review", "triage.reply", "triage.ignore"),
     lambda s, a, c, f: s.noted("triage", _k(f))),
    ("only_opener_can_ask", ("triage.ask",), lambda s, a, c, f: s.opener == a),
    ("adviser_must_not_be_the_opener", ("triage.ask",), lambda s, a, c, f: s.opener != f["adviser_id"]),
    ("adviser_is_asked_once", ("triage.ask",), lambda s, a, c, f: not s.contains(("adviser", _k(f), f["adviser_id"]))),
    ("adviser_must_not_be_a_reviewer", ("triage.ask",), lambda s, a, c, f: not s.contains(("reviewer", _k(f), f["adviser_id"]))),
    ("triage_must_not_be_reviewed", ("triage.ask", "triage.advise"), lambda s, a, c, f: not s.noted("reviewer", _k(f))),
    ("only_asked_advisers_can_advise", ("triage.advise",), lambda s, a, c, f: s.contains(("adviser", _k(f), a))),
    ("adviser_advises_once", ("triage.advise",), lambda s, a, c, f: not s.contains(("advice", _k(f), a))),
    ("reviewer_must_not_be_an_adviser", ("triage.review",), lambda s, a, c, f: not s.contains(("adviser", _k(f), a))),
    ("reviewer_must_not_be_the_opener", ("triage.review",), lambda s, a, c, f: s.opener != a),
    ("only_opener_can_decide", ("triage.reply", "triage.ignore"), lambda s, a, c, f: s.opener == a),
    ("triage_is_decided_once", ("triage.reply", "triage.ignore"), lambda s, a, c, f: not s.decided(_k(f))),
    ("triage_must_be_undecided", ("triage.ask", "triage.advise", "triage.review"), lambda s, a, c, f: not s.decided(_k(f))),
]
RULE_NAMES = [r[0] for r in RULES]
ADMISSION = ("stream_must_exist", "stream_must_be_open")


def rules_of(cmd: str, order=None):
    return [r[0] for r in (order or RULES) if cmd in r[1]]


def expected_rules(cmd: str):
    if cmd == "stream.open":
        return ["stream_id_must_be_new", "revision_url_must_name_a_commit"]
    if cmd == "stream.close":
        return list(ADMISSION) + ["only_opener_can_close"]
    return list(ADMISSION) + rules_of(cmd)


def judge(stream: Stream, request: dict, order=None) -> str | None:
    if not well_formed(request):
        return "malformed"
    actor, cmd, fresh = request["actor_id"], request["command"], request["fresh"]
    name = cmd["command"]
    if len(fresh) != FRESH.get(name, 0):
        return "fresh_ids_must_match_the_command"
    if name == "stream.open":
        if stream.opened:
            return "stream_id_must_be_new"
        if not valid_revision_url(cmd["proof_revision_url"]):
            return "revision_url_must_name_a_commit"
        return None
    if not stream.opened:
        return "stream_must_exist"
    if stream.closed:
        return "stream_must_be_open"
    if name == "stream.close":
        return None if actor == stream.opener else "only_opener_can_close"
    for reason, commands, holds in (order or RULES):
        if name in commands and not holds(stream, actor, name, cmd):
            return reason
    return None


def event_of(request: dict, stream_id: str) -> dict:
    cmd = request["command"]
    e = {"event": EVENT_OF[cmd["command"]], "stream_id": stream_id, "actor_id": request["actor_id"], "meta": cmd.get("meta")}
    e.update({k: v for k, v in cmd.items() if k not in ("command", "stream_id", "meta")})
    return e


def notes_of(event: dict):
    name, k = event["event"], event.get("triage_id")
    if name == "triage.created":
        return [("triage", k, event["message_url"])]
    if name == "triage.asked":
        return [("adviser", k, event["adviser_id"])]
    if name == "triage.advised":
        return [("advice", k, event["actor_id"]), ("verdict", k, event["verdict"])]
    if name == "triage.reviewed":
        return [("reviewer", k, event["actor_id"]), ("call", k, event["verdict"])]
    if name == "triage.replied":
        return [("replied", k, event["email_id"])]
    if name == "triage.ignored":
        return [("ignored", k, "")]
    return []


def apply(stream: Stream, event: dict) -> None:
    if event["event"] == "stream.opened":
        stream.opened, stream.opener, stream.url = True, event["actor_id"], event["proof_revision_url"]
    elif event["event"] == "stream.closed":
        stream.closed = True
    stream.notes.extend(notes_of(event))
    stream.events.append(event)


def stream_of(request: dict) -> str | None:
    cmd = request["command"]
    if cmd["command"] == "stream.open":
        return request["fresh"][0] if request["fresh"] else ""
    return cmd.get("stream_id")


class Model:
    def __init__(self):
        self.streams = {}

    def stream(self, sid: str) -> Stream:
        if sid not in self.streams:
            self.streams[sid] = Stream(sid)
        return self.streams[sid]

    def step(self, request: dict, order=None):
        if not well_formed(request):
            return "malformed", None, None, None
        sid = stream_of(request)
        s = self.stream(sid)
        want = judge(s, request, order)
        at = len(s.events)
        if want is not None:
            return want, sid, at, None
        e = event_of(request, sid)
        apply(s, e)
        return None, sid, at, e
