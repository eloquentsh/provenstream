# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""A Python restatement of what the email engine does with one request: the wire's decoding (what is `malformed`),
the core's admission, the layer's fifteen rules in the engine's order, the event an accepted request becomes, and the
notes it leaves. The oracle every test in this directory judges the engine by.

It is written from Email/Layer.lean and the core (Provenstream/Event.lean, Schema.lean, Json.lean), not imported from
them, so a difference between the two is a finding. `RULES` is the layer's list, in its order, each rule a predicate
over the stream's view, its notes and the would-be event; `judge` tries them as the engine does and answers the first
that refuses.
"""
from __future__ import annotations
import re

PROOF_URL = "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/email"

# -- the schema: each command's fields, in order, with their kinds (cross-checked against the engine's description) -----

SCHEMA = {
    "stream.open": [("proof_revision_url", "text"), ("meta", "meta")],
    "stream.close": [("stream_id", "uuid"), ("meta", "meta")],
    "email.create": [("stream_id", "uuid"), ("email_id", "uuid"), ("in_reply_to_url", "eml?"), ("meta", "meta")],
    "email.solicit": [("stream_id", "uuid"), ("email_id", "uuid"), ("drafter_id", "uuid"), ("meta", "meta")],
    "email.draft": [("stream_id", "uuid"), ("email_id", "uuid"), ("draft_url", "eml"), ("meta", "meta")],
    "email.compose": [("stream_id", "uuid"), ("email_id", "uuid"), ("composed_url", "eml"), ("screen_url", "url"),
                      ("meta", "meta")],
    "email.send": [("stream_id", "uuid"), ("email_id", "uuid"), ("sent_url", "eml"), ("meta", "meta")],
    "email.discard": [("stream_id", "uuid"), ("email_id", "uuid"), ("meta", "meta")],
}
EVENT_OF = {"stream.open": "stream.opened", "stream.close": "stream.closed", "email.create": "email.created",
            "email.solicit": "email.solicited", "email.draft": "email.drafted", "email.compose": "email.composed",
            "email.send": "email.sent", "email.discard": "email.discarded"}
FRESH = {"stream.open": 1}
LAYER = tuple(c for c in SCHEMA if c.startswith("email."))
CORE = ("stream.open", "stream.close")
COMMANDS = CORE + LAYER
EML_NOTES = ("reply_to", "draft", "composed", "sent")
EML_FIELD = {"email.create": "in_reply_to_url", "email.draft": "draft_url", "email.compose": "composed_url",
             "email.send": "sent_url"}

# -- forms (Provenstream/Event.lean; the wire refuses a field not of its form as `malformed`) --------------------------

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
    """The layer's `validUrl`: a scheme, `://` and something after it; nothing at or below a space, no DEL; at most
    2048 characters (characters, not bytes)."""
    if not isinstance(s, str) or len(s) > 2048 or not all(32 < ord(c) and ord(c) != 127 for c in s):
        return False
    parts = s.split("://")
    return len(parts) == 2 and bool(parts[0]) and bool(parts[1])


def valid_eml(s) -> bool:
    """The layer's `validEml`: a URL ending in `.eml`."""
    return valid_url(s) and s.endswith(".eml")


def _alnum(c: str) -> bool:
    return ("a" <= c <= "z") or ("A" <= c <= "Z") or ("0" <= c <= "9")


def valid_revision(s: str) -> bool:
    return len(s) in (40, 64) and bool(HEX.match(s))


def valid_segment(seg: str) -> bool:
    return seg not in ("", ".", "..") and all(_alnum(c) or c in "._-" for c in seg)


def valid_revision_url(s) -> bool:
    """The core's `validRevisionUrl`: a repository URL, then `/commit/`, `#` or `@` and a full lowercase hex commit, or
    `/tree/`, the commit, `/` and a package path."""
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
    """Whether the engine decodes the request at all: `actor_id`, `command` and `fresh` present and of their forms,
    a known command with exactly its keys (`meta` and a `?` kind may be absent), each value of its kind."""
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
        if kind == "url" and not valid_url(v):
            return False
        if kind == "eml" and not valid_eml(v):
            return False
        if kind == "eml?" and v is not None and not valid_eml(v):
            return False
        if kind == "text" and not (isinstance(v, str) and "\x00" not in v):
            return False
        if kind == "meta" and not valid_meta(v):
            return False
    return True


# -- the stream, as the rules see it -----------------------------------------------------------------------------------

class Stream:
    """One stream: the core's view of it, the layer's notes, and the accepted events in order."""

    def __init__(self, sid: str):
        self.id = sid
        self.opened = False
        self.closed = False
        self.opener = None
        self.url = None
        self.notes = []       # (what, email_id, who_or_eml)
        self.events = []      # accepted events, core and layer, in order, as the engine returns them

    def noted(self, what, k):
        return any(n[0] == what and n[1] == k for n in self.notes)

    def contains(self, note):
        return note in self.notes

    def decided(self, k):
        return self.noted("sent", k) or self.noted("discarded", k)

    def composed(self, k):
        return self.noted("composed", k)

    def eml_named(self, k, u):
        return any(n[0] in EML_NOTES and n[1] == k and n[2] == u for n in self.notes)

    def emls(self, k):
        return [n[2] for n in self.notes if n[0] in EML_NOTES and n[1] == k]

    def emails(self):
        return [n[1] for n in self.notes if n[0] == "email"]

    def drafters(self, k):
        return [n[2] for n in self.notes if n[0] == "drafter" and n[1] == k]

    def composers(self, k):
        return [n[2] for n in self.notes if n[0] == "composer" and n[1] == k]

    def undecided(self):
        return [k for k in self.emails() if not self.decided(k)]

    def pairs(self, what, who):
        return [{"email_id": n[1], who: n[2]} for n in self.notes if n[0] == what]

    def items(self, what):
        return [n[1] for n in self.notes if n[0] == what]

    def read(self):
        """What `{"query": "stream"}` answers."""
        if not self.opened:
            return {"error": "stream_must_exist"}
        return {"stream_id": self.id, "proof_revision_url": self.url, "opener_id": self.opener,
                "closed": self.closed,
                "emails": self.items("email"),
                "replies_to": self.pairs("reply_to", "in_reply_to_url"),
                "drafters": self.pairs("drafter", "drafter_id"),
                "drafts": self.pairs("draft", "draft_url"),
                "composers": self.pairs("composer", "composer_id"),
                "composed": self.pairs("composed", "composed_url"),
                "sent": self.pairs("sent", "sent_url"),
                "discarded": self.items("discarded")}


# -- the layer's rules, in the engine's order (Layer.lean `rules`) ----------------------------------------------------
# Each: (reason, the commands it is tried on, holds(stream, actor, command, fields) -> bool).

def _k(f):
    return f["email_id"]


RULES = [
    ("only_opener_can_create", ("email.create",), lambda s, a, c, f: s.opener == a),
    ("email_id_must_be_new", ("email.create",), lambda s, a, c, f: not s.noted("email", _k(f))),
    ("email_must_exist", ("email.solicit", "email.draft", "email.compose", "email.send", "email.discard"),
     lambda s, a, c, f: s.noted("email", _k(f))),
    ("eml_urls_must_be_unique", ("email.draft", "email.compose", "email.send"),
     lambda s, a, c, f: not s.eml_named(_k(f), f[EML_FIELD[c]])),
    ("only_opener_can_solicit", ("email.solicit",), lambda s, a, c, f: s.opener == a),
    ("drafter_must_not_be_the_opener", ("email.solicit",), lambda s, a, c, f: s.opener != f["drafter_id"]),
    ("drafter_is_solicited_once", ("email.solicit",),
     lambda s, a, c, f: not s.contains(("drafter", _k(f), f["drafter_id"]))),
    ("drafter_must_not_be_a_composer", ("email.solicit",),
     lambda s, a, c, f: not s.contains(("composer", _k(f), f["drafter_id"]))),
    ("email_must_not_be_composed", ("email.solicit", "email.draft"), lambda s, a, c, f: not s.noted("composed", _k(f))),
    ("only_solicited_drafters_can_draft", ("email.draft",), lambda s, a, c, f: s.contains(("drafter", _k(f), a))),
    ("composer_must_not_be_a_drafter", ("email.compose",), lambda s, a, c, f: not s.contains(("drafter", _k(f), a))),
    ("composer_must_not_be_the_opener", ("email.compose",), lambda s, a, c, f: s.opener != a),
    ("only_opener_can_decide", ("email.send", "email.discard"), lambda s, a, c, f: s.opener == a),
    ("email_is_decided_once", ("email.send", "email.discard"), lambda s, a, c, f: not s.decided(_k(f))),
    ("email_must_be_undecided", ("email.solicit", "email.draft", "email.compose"),
     lambda s, a, c, f: not s.decided(_k(f))),
]
RULE_NAMES = [r[0] for r in RULES]
ADMISSION = ("stream_must_exist", "stream_must_be_open")


def rules_of(cmd: str, order=None):
    """The layer's rule names tried on `cmd`, in the engine's order (`order`: another order of RULES, for a mutant)."""
    return [r[0] for r in (order or RULES) if cmd in r[1]]


def expected_rules(cmd: str):
    """What the engine's description lists as the rules of `cmd`: the core's for its commands, the admission then the
    layer's for a layer command."""
    if cmd == "stream.open":
        return ["stream_id_must_be_new", "revision_url_must_name_a_commit"]
    if cmd == "stream.close":
        return list(ADMISSION) + ["only_opener_can_close"]
    return list(ADMISSION) + rules_of(cmd)


def failing_rules(stream: Stream, actor: str, cmd: str, f: dict, order=None):
    """Every layer rule of `cmd` that fails, in order (not only the first). Only for a layer command that was admitted."""
    return [r[0] for r in (order or RULES) if cmd in r[1] and not r[2](stream, actor, cmd, f)]


def judge(stream: Stream, request: dict, order=None) -> str | None:
    """The engine's answer to `request` on `stream`: 'malformed', the reason it refuses, or None (accepted). `order`
    is RULES in another order, for a mutant's prediction."""
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
    """The event an accepted request becomes: the command's params under the event's name, plus `actor_id`, `meta`
    and every optional field (null when absent) and, for an open, the minted `stream_id`."""
    cmd = request["command"]
    e = {"event": EVENT_OF[cmd["command"]], "stream_id": stream_id, "actor_id": request["actor_id"],
         "meta": cmd.get("meta")}
    e.update({k: v for k, v in cmd.items() if k not in ("command", "stream_id", "meta")})
    for name, kind in SCHEMA[cmd["command"]]:
        if kind.endswith("?"):
            e.setdefault(name, None)
    return e


def notes_of(event: dict):
    """The notes an accepted layer event leaves (Layer.lean `notes`)."""
    name, k = event["event"], event.get("email_id")
    if name == "email.created":
        reply = event.get("in_reply_to_url")
        return [("email", k, "")] + ([("reply_to", k, reply)] if reply is not None else [])
    if name == "email.solicited":
        return [("drafter", k, event["drafter_id"])]
    if name == "email.drafted":
        return [("draft", k, event["draft_url"])]
    if name == "email.composed":
        return [("composer", k, event["actor_id"]), ("composed", k, event["composed_url"])]
    if name == "email.sent":
        return [("sent", k, event["sent_url"])]
    if name == "email.discarded":
        return [("discarded", k, "")]
    return []


def apply(stream: Stream, event: dict) -> None:
    """Record an accepted event on the model's stream."""
    if event["event"] == "stream.opened":
        stream.opened, stream.opener, stream.url = True, event["actor_id"], event["proof_revision_url"]
    elif event["event"] == "stream.closed":
        stream.closed = True
    stream.notes.extend(notes_of(event))
    stream.events.append(event)


def stream_of(request: dict) -> str | None:
    """The stream a well-formed request is on: for an open the first fresh id (the stream `""` when there is none), else
    the command's `stream_id`."""
    cmd = request["command"]
    if cmd["command"] == "stream.open":
        return request["fresh"][0] if request["fresh"] else ""
    return cmd.get("stream_id")


class Model:
    """Several streams, judged and updated as the engine would be. `step` answers what the engine will say and, when
    it accepts, records the event."""

    def __init__(self):
        self.streams = {}

    def stream(self, sid: str) -> Stream:
        if sid not in self.streams:
            self.streams[sid] = Stream(sid)
        return self.streams[sid]

    def step(self, request: dict, order=None):
        """`(want, stream_id, at, event)`: the reason or 'malformed' or None; the stream; the position; the event an
        acceptance appends (None otherwise). The model is updated on acceptance."""
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
