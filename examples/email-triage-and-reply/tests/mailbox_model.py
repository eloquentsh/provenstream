# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""A Python restatement of what the email-triage-and-reply engine does with one request. It covers the wire's
decoding (what is `malformed`), the core's admission and the layer's forty rules in the engine's order. It also
gives the event an accepted request becomes and the notes it leaves. Every test in this directory judges the engine
by it.

It is written from EmailTriageAndReply/Layer.lean and the core, not imported from them. A difference between the two
is a finding. One list of notes holds the delegation's, the email's and the triage's. `RULES` is the layer's list, in
its order. `judge` tries them as the engine does and answers the first that refuses.
"""
from __future__ import annotations
import re

PROOF_URL = "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/email-triage-and-reply"

# -- the schema: each command's fields, in order, with their kinds (cross-checked against the engine's description) -----

SCHEMA = {
    "stream.open": [("proof_revision_url", "text"), ("meta", "meta")],
    "stream.close": [("stream_id", "uuid"), ("meta", "meta")],
    "principal.invite": [("stream_id", "uuid"), ("principal_id", "uuid"), ("meta", "meta")],
    "principal.summon": [("stream_id", "uuid"), ("principal_id", "uuid"), ("meta", "meta")],
    "principal.delegate": [("stream_id", "uuid"), ("delegate_id", "uuid"), ("meta", "meta")],
    "email.create": [("stream_id", "uuid"), ("email_id", "uuid"), ("in_reply_to_eml_url", "eml?"), ("meta", "meta")],
    "email.solicit": [("stream_id", "uuid"), ("email_id", "uuid"), ("preparer_id", "uuid"), ("meta", "meta")],
    "email.prepare": [("stream_id", "uuid"), ("email_id", "uuid"), ("preparation_url", "url"), ("meta", "meta")],
    "email.draft": [("stream_id", "uuid"), ("email_id", "uuid"), ("draft_eml_url", "eml"), ("screen_url", "url"),
                    ("meta", "meta")],
    "email.send": [("stream_id", "uuid"), ("email_id", "uuid"), ("sent_eml_url", "eml"), ("meta", "meta")],
    "email.discard": [("stream_id", "uuid"), ("email_id", "uuid"), ("meta", "meta")],
    "triage.request": [("stream_id", "uuid"), ("triage_id", "uuid"), ("message_eml_url", "eml"), ("meta", "meta")],
    "triage.ask": [("stream_id", "uuid"), ("triage_id", "uuid"), ("adviser_id", "uuid"), ("meta", "meta")],
    "triage.advise": [("stream_id", "uuid"), ("triage_id", "uuid"), ("verdict", "verdict"), ("meta", "meta")],
    "triage.consider": [("stream_id", "uuid"), ("triage_id", "uuid"), ("verdict", "verdict"), ("meta", "meta")],
    "triage.reply": [("stream_id", "uuid"), ("triage_id", "uuid"), ("email_id", "uuid"), ("meta", "meta")],
    "triage.work": [("stream_id", "uuid"), ("triage_id", "uuid"), ("work_id", "uuid"), ("meta", "meta")],
    "triage.ignore": [("stream_id", "uuid"), ("triage_id", "uuid"), ("meta", "meta")],
    "triage.defer": [("stream_id", "uuid"), ("triage_id", "uuid"), ("meta", "meta")],
}
EVENT_OF = {"stream.open": "stream.opened", "stream.close": "stream.closed",
            "principal.invite": "principal.invited", "principal.summon": "principal.summoned",
            "principal.delegate": "principal.delegated",
            "email.create": "email.created", "email.solicit": "email.solicited", "email.prepare": "email.prepared",
            "email.draft": "email.drafted", "email.send": "email.sent", "email.discard": "email.discarded",
            "triage.request": "triage.requested", "triage.ask": "triage.asked", "triage.advise": "triage.advised",
            "triage.consider": "triage.considered", "triage.reply": "triage.replied", "triage.work": "triage.worked",
            "triage.ignore": "triage.ignored", "triage.defer": "triage.deferred"}
FRESH = {"stream.open": 1}
PRINCIPAL = tuple(c for c in SCHEMA if c.startswith("principal."))
EMAIL = tuple(c for c in SCHEMA if c.startswith("email."))
TRIAGE = tuple(c for c in SCHEMA if c.startswith("triage."))
LAYER = PRINCIPAL + EMAIL + TRIAGE
CORE = ("stream.open", "stream.close")
COMMANDS = CORE + LAYER
EML_NOTES = ("reply_to", "draft", "sent")
EML_FIELD = {"email.create": "in_reply_to_eml_url", "email.draft": "draft_eml_url", "email.send": "sent_eml_url"}
VERDICTS = ("reply", "work", "ignore", "defer")

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


def valid_verdict(s) -> bool:
    """The layer's `validVerdict`: exactly `reply`, `work` or `ignore`."""
    return isinstance(s, str) and s in VERDICTS


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
        if kind == "verdict" and not valid_verdict(v):
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
        self.notes = []       # (what, principal or email_id or triage_id, who_or_which)
        self.events = []      # accepted events, core and layer, in order, as the engine returns them

    def noted(self, what, k):
        return any(n[0] == what and n[1] == k for n in self.notes)

    def contains(self, note):
        return note in self.notes

    def items(self, what):
        return [n[1] for n in self.notes if n[0] == what]

    def thirds(self, what, k):
        return [n[2] for n in self.notes if n[0] == what and n[1] == k]

    def pairs(self, what, key, who):
        return [{key: n[1], who: n[2]} for n in self.notes if n[0] == what]

    # the principals': persons, agents and delegations (a delegation lasts for the stream's life)
    def is_delegate_of(self, o, d):
        return ("delegate", o, d) in self.notes

    def has_delegator(self, d):
        return any(n[0] == "delegate" and n[2] == d for n in self.notes)

    def delegator(self, d):
        return next((n[1] for n in self.notes if n[0] == "delegate" and n[2] == d), None)

    def invited(self, p):
        return self.noted("invited", p)

    def summoned(self, p):
        return self.noted("summoned", p)

    def declared(self, p):
        return self.invited(p) or self.summoned(p)

    def is_person(self, a):
        return a == self.opener or self.invited(a)

    def is_new(self, p):
        return not self.invited(p) and not self.summoned(p) and p != self.opener

    def for_owner(self, a):
        """The owner (the opener) or a delegate of the owner."""
        return self.opener is not None and (a == self.opener or self.is_delegate_of(self.opener, a))

    def person_for_owner(self, a):
        """The owner, or a delegate of the owner who is a person: who makes the terminal decisions."""
        return self.opener is not None and (a == self.opener or (self.is_delegate_of(self.opener, a) and self.invited(a)))

    def delegates(self):
        return [n[2] for n in self.notes if n[0] == "delegate" and n[1] == self.opener]

    # the email's
    def email_decided(self, k):
        return self.noted("sent", k) or self.noted("discarded", k)

    def drafted(self, k):
        return self.noted("draft", k)

    def eml_named(self, k, u):
        return any(n[0] in EML_NOTES and n[1] == k and n[2] == u for n in self.notes)

    def emls(self, k):
        return [n[2] for n in self.notes if n[0] in EML_NOTES and n[1] == k]

    def emails(self):
        return self.items("email")

    def preparers(self, k):
        return self.thirds("preparer", k)

    def drafters(self, k):
        return self.thirds("drafter", k)

    def undecided_emails(self):
        return [k for k in self.emails() if not self.email_decided(k)]

    # the triage's
    def triage_decided(self, k):
        return any(self.noted(w, k) for w in ("replied", "worked", "ignored", "deferred"))

    def considered(self, k):
        return self.noted("considerer", k)

    def triages(self):
        return self.items("triage")

    def advisers(self, k):
        return self.thirds("adviser", k)

    def advised(self, k):
        return self.thirds("advice", k)

    def considerers(self, k):
        return self.thirds("considerer", k)

    def undecided_triages(self):
        return [k for k in self.triages() if not self.triage_decided(k)]

    # the reply rule's
    def reply_claimed(self, e):
        return any(n[0] == "replied" and n[2] == e for n in self.notes)

    def unclaimed_emails(self):
        return [e for e in self.emails() if not self.reply_claimed(e)]

    def read(self):
        """What `{"query": "stream"}` answers."""
        if not self.opened:
            return {"error": "stream_must_exist"}
        return {"stream_id": self.id, "proof_revision_url": self.url, "opener_id": self.opener,
                "closed": self.closed,
                "invited": self.items("invited"),
                "summoned": self.items("summoned"),
                "delegations": self.pairs("delegate", "delegator_id", "delegate_id"),
                "emails": self.items("email"),
                "replies_to": self.pairs("reply_to", "email_id", "in_reply_to_eml_url"),
                "preparers": self.pairs("preparer", "email_id", "preparer_id"),
                "preparations": self.pairs("preparation", "email_id", "preparation_url"),
                "drafters": self.pairs("drafter", "email_id", "drafter_id"),
                "drafts": self.pairs("draft", "email_id", "draft_eml_url"),
                "sent": self.pairs("sent", "email_id", "sent_eml_url"),
                "discarded": self.items("discarded"),
                "triages": self.pairs("triage", "triage_id", "message_eml_url"),
                "advisers": self.pairs("adviser", "triage_id", "adviser_id"),
                "advice": self.pairs("advice", "triage_id", "adviser_id"),
                "verdicts": self.pairs("verdict", "triage_id", "verdict"),
                "considerers": self.pairs("considerer", "triage_id", "considerer_id"),
                "considerations": self.pairs("consideration", "triage_id", "verdict"),
                "replied": self.pairs("replied", "triage_id", "email_id"),
                "worked": self.pairs("worked", "triage_id", "work_id"),
                "ignored": self.items("ignored"),
                "deferred": self.items("deferred")}


# -- the layer's rules, in the engine's order (Layer.lean `rules`) ----------------------------------------------------
# Each: (reason, the commands it is tried on, holds(stream, actor, command, fields) -> bool).

def _k(f):
    return f["email_id"]


def _t(f):
    return f["triage_id"]


PRINCIPAL_RULES = [
    ("only_opener_or_delegates_can_invite", ("principal.invite",), lambda s, a, c, f: s.for_owner(a)),
    ("only_opener_or_delegates_can_summon", ("principal.summon",), lambda s, a, c, f: s.for_owner(a)),
    ("principal_must_be_new", ("principal.invite", "principal.summon"), lambda s, a, c, f: s.is_new(f["principal_id"])),
    ("only_persons_can_delegate", ("principal.delegate",), lambda s, a, c, f: s.is_person(a)),
    ("delegate_must_be_declared", ("principal.delegate",), lambda s, a, c, f: s.declared(f["delegate_id"])),
    ("delegate_must_not_be_the_delegator", ("principal.delegate",), lambda s, a, c, f: a != f["delegate_id"]),
    ("delegate_must_be_new", ("principal.delegate",), lambda s, a, c, f: not s.has_delegator(f["delegate_id"])),
]
EMAIL_RULES = [
    ("only_opener_or_delegates_can_create", ("email.create",), lambda s, a, c, f: s.for_owner(a)),
    ("email_id_must_be_new", ("email.create",), lambda s, a, c, f: not s.noted("email", _k(f))),
    ("email_must_exist", ("email.solicit", "email.prepare", "email.draft", "email.send", "email.discard"),
     lambda s, a, c, f: s.noted("email", _k(f))),
    ("eml_urls_must_be_unique", ("email.draft", "email.send"),
     lambda s, a, c, f: not s.eml_named(_k(f), f[EML_FIELD[c]])),
    ("only_owner_or_delegates_can_solicit", ("email.solicit",), lambda s, a, c, f: s.for_owner(a)),
    ("preparer_must_not_be_the_owner", ("email.solicit",), lambda s, a, c, f: s.opener != f["preparer_id"]),
    ("preparer_must_be_declared", ("email.solicit",), lambda s, a, c, f: s.declared(f["preparer_id"])),
    ("preparer_must_not_be_the_soliciter", ("email.solicit",), lambda s, a, c, f: a != f["preparer_id"]),
    ("preparer_is_solicited_once", ("email.solicit",),
     lambda s, a, c, f: not s.contains(("preparer", _k(f), f["preparer_id"]))),
    ("preparer_must_not_be_a_drafter", ("email.solicit",),
     lambda s, a, c, f: not s.contains(("drafter", _k(f), f["preparer_id"]))),
    ("only_solicited_preparers_can_prepare", ("email.prepare",), lambda s, a, c, f: s.contains(("preparer", _k(f), a))),
    ("drafter_must_not_be_a_preparer", ("email.draft",), lambda s, a, c, f: not s.contains(("preparer", _k(f), a))),
    ("only_owner_or_delegates_can_draft", ("email.draft",), lambda s, a, c, f: s.for_owner(a)),
    ("only_owner_or_person_delegates_can_decide", ("email.send", "email.discard"),
     lambda s, a, c, f: s.person_for_owner(a)),
    ("email_is_decided_once", ("email.send", "email.discard"), lambda s, a, c, f: not s.email_decided(_k(f))),
    ("email_must_be_undecided", ("email.solicit", "email.prepare", "email.draft"),
     lambda s, a, c, f: not s.email_decided(_k(f))),
]
DECISIONS = ("triage.reply", "triage.work", "triage.ignore", "triage.defer")
TRIAGE_RULES = [
    ("only_opener_or_delegates_can_request", ("triage.request",), lambda s, a, c, f: s.for_owner(a)),
    ("triage_id_must_be_new", ("triage.request",), lambda s, a, c, f: not s.noted("triage", _t(f))),
    ("triage_must_exist", ("triage.ask", "triage.advise", "triage.consider") + DECISIONS,
     lambda s, a, c, f: s.noted("triage", _t(f))),
    ("only_owner_or_delegates_can_ask", ("triage.ask",), lambda s, a, c, f: s.for_owner(a)),
    ("adviser_must_not_be_the_owner", ("triage.ask",), lambda s, a, c, f: s.opener != f["adviser_id"]),
    ("adviser_must_be_declared", ("triage.ask",), lambda s, a, c, f: s.declared(f["adviser_id"])),
    ("adviser_must_not_be_the_asker", ("triage.ask",), lambda s, a, c, f: a != f["adviser_id"]),
    ("adviser_is_asked_once", ("triage.ask",), lambda s, a, c, f: not s.contains(("adviser", _t(f), f["adviser_id"]))),
    ("adviser_must_not_be_a_considerer", ("triage.ask",),
     lambda s, a, c, f: not s.contains(("considerer", _t(f), f["adviser_id"]))),
    ("only_asked_advisers_can_advise", ("triage.advise",), lambda s, a, c, f: s.contains(("adviser", _t(f), a))),
    ("adviser_advises_once", ("triage.advise",), lambda s, a, c, f: not s.contains(("advice", _t(f), a))),
    ("considerer_must_not_be_an_adviser", ("triage.consider",),
     lambda s, a, c, f: not s.contains(("adviser", _t(f), a))),
    ("only_owner_or_delegates_can_consider", ("triage.consider",), lambda s, a, c, f: s.for_owner(a)),
    ("only_owner_or_person_delegates_can_decide", DECISIONS, lambda s, a, c, f: s.person_for_owner(a)),
    ("triage_is_decided_once", DECISIONS, lambda s, a, c, f: not s.triage_decided(_t(f))),
    ("triage_must_be_undecided", ("triage.ask", "triage.advise", "triage.consider"),
     lambda s, a, c, f: not s.triage_decided(_t(f))),
]
# the reply's email exists on this stream, and no earlier reply names it
REPLY_RULES = [
    ("reply_must_name_an_unclaimed_email", ("triage.reply",),
     lambda s, a, c, f: s.noted("email", f["email_id"]) and not s.reply_claimed(f["email_id"])),
]
RULES = PRINCIPAL_RULES + EMAIL_RULES + TRIAGE_RULES + REPLY_RULES
RULE_NAMES = [r[0] for r in RULES]
ADMISSION = ("stream_must_exist", "stream_must_be_open")


def rules_of(cmd: str, order=None):
    """The layer's rule names tried on `cmd`, in the engine's order."""
    return [r[0] for r in (order or RULES) if cmd in r[1]]


def expected_rules(cmd: str):
    """What the engine's description lists as the rules of `cmd`: the core's for its commands, the admission then the
    layer's for a layer command."""
    if cmd == "stream.open":
        return ["stream_id_must_be_new", "revision_url_must_name_a_commit"]
    if cmd == "stream.close":
        return list(ADMISSION) + ["only_opener_can_close"]
    return list(ADMISSION) + rules_of(cmd)


def failing_rules(stream: Stream, actor: str, cmd: str, f: dict):
    """Every layer rule of `cmd` that fails, in order (not only the first). Only for a layer command that was admitted."""
    return [r[0] for r in RULES if cmd in r[1] and not r[2](stream, actor, cmd, f)]


def judge(stream: Stream, request: dict, order=None) -> str | None:
    """The engine's answer to `request` on `stream`: 'malformed', the reason it refuses, or None (accepted)."""
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
    name = event["event"]
    k, t = event.get("email_id"), event.get("triage_id")
    if name == "principal.invited":
        return [("invited", event["principal_id"], "")]
    if name == "principal.summoned":
        return [("summoned", event["principal_id"], "")]
    if name == "principal.delegated":
        return [("delegate", event["actor_id"], event["delegate_id"])]
    if name == "email.created":
        reply = event.get("in_reply_to_eml_url")
        return [("email", k, event["actor_id"])] + ([("reply_to", k, reply)] if reply is not None else [])
    if name == "email.solicited":
        return [("preparer", k, event["preparer_id"])]
    if name == "email.prepared":
        return [("preparation", k, event["preparation_url"])]
    if name == "email.drafted":
        return [("drafter", k, event["actor_id"]), ("draft", k, event["draft_eml_url"])]
    if name == "email.sent":
        return [("sent", k, event["sent_eml_url"])]
    if name == "email.discarded":
        return [("discarded", k, "")]
    if name == "triage.requested":
        return [("triage", t, event["message_eml_url"])]
    if name == "triage.asked":
        return [("adviser", t, event["adviser_id"])]
    if name == "triage.advised":
        return [("advice", t, event["actor_id"]), ("verdict", t, event["verdict"])]
    if name == "triage.considered":
        return [("considerer", t, event["actor_id"]), ("consideration", t, event["verdict"])]
    if name == "triage.replied":
        return [("replied", t, event["email_id"])]
    if name == "triage.worked":
        return [("worked", t, event["work_id"])]
    if name == "triage.ignored":
        return [("ignored", t, "")]
    if name == "triage.deferred":
        return [("deferred", t, "")]
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
