# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""A Python restatement of what the solochangecontrol engine does with one request: the wire's decoding (what is
`malformed`), the core's admission, the layer's seventeen rules in the engine's order, the event an accepted request
becomes, and the notes it leaves. The oracle every test in this directory judges the engine by.

It is written from SoloChangeControl/Layer.lean and the core (Provenstream/Event.lean, Schema.lean, Json.lean), not
imported from them, so a difference between the two is a finding. `RULES` is the layer's list, in its order, each
rule a predicate over the stream's view, its notes and the would-be event; `judge` tries them as the engine does and
answers the first that refuses.
"""
from __future__ import annotations
import re

PROOF_URL = "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol"

# -- the schema: each command's fields, in order, with their kinds (cross-checked against the engine's description) -----

SCHEMA = {
    "stream.open": [("proof_revision_url", "text"), ("meta", "meta")],
    "stream.close": [("stream_id", "uuid"), ("meta", "meta")],
    "change.create": [("stream_id", "uuid"), ("change_id", "uuid"), ("from_revision_url", "url"),
                      ("harness_revision_url", "url?"), ("meta", "meta")],
    "change.branch": [("stream_id", "uuid"), ("change_id", "uuid"), ("developer_id", "uuid"),
                      ("branch_revision_url", "url"), ("meta", "meta")],
    "change.push": [("stream_id", "uuid"), ("change_id", "uuid"), ("pushed_revision_url", "url"), ("meta", "meta")],
    "change.pull": [("stream_id", "uuid"), ("change_id", "uuid"), ("meta", "meta")],
    "change.review": [("stream_id", "uuid"), ("change_id", "uuid"), ("reviewed_revision_url", "url"),
                      ("screen_url", "url"), ("meta", "meta")],
    "change.merge": [("stream_id", "uuid"), ("change_id", "uuid"), ("merged_revision_url", "url"), ("meta", "meta")],
    "change.abandon": [("stream_id", "uuid"), ("change_id", "uuid"), ("meta", "meta")],
}
EVENT_OF = {"stream.open": "stream.opened", "stream.close": "stream.closed", "change.create": "change.created",
            "change.branch": "change.branched", "change.push": "change.pushed", "change.pull": "change.pulled",
            "change.review": "change.reviewed", "change.merge": "change.merged", "change.abandon": "change.abandoned"}
FRESH = {"stream.open": 1}
LAYER = tuple(c for c in SCHEMA if c.startswith("change."))
CORE = ("stream.open", "stream.close")
COMMANDS = CORE + LAYER
REVISION_NOTES = ("change", "branch", "pushed", "reviewed", "merged")
REVISION_FIELD = {"change.create": "from_revision_url", "change.branch": "branch_revision_url",
                  "change.push": "pushed_revision_url", "change.review": "reviewed_revision_url",
                  "change.merge": "merged_revision_url"}

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
        if kind == "url?" and v is not None and not valid_url(v):
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
        self.notes = []       # (what, change_id, who_or_revision)
        self.events = []      # accepted events, core and layer, in order, as the engine returns them

    def noted(self, what, k):
        return any(n[0] == what and n[1] == k for n in self.notes)

    def contains(self, note):
        return note in self.notes

    def decided(self, k):
        return self.noted("merged", k) or self.noted("abandoned", k)

    def revision_named(self, k, u):
        return any(n[0] in REVISION_NOTES and n[1] == k and n[2] == u for n in self.notes)

    def revisions(self, k):
        return [n[2] for n in self.notes if n[0] in REVISION_NOTES and n[1] == k]

    def changes(self):
        return [n[1] for n in self.notes if n[0] == "change"]

    def developers(self, k):
        return [n[2] for n in self.notes if n[0] == "developer" and n[1] == k]

    def reviewers(self, k):
        return [n[2] for n in self.notes if n[0] == "reviewer" and n[1] == k]

    def undecided(self):
        return [k for k in self.changes() if not self.decided(k)]

    def pairs(self, what, who):
        return [{"change_id": n[1], who: n[2]} for n in self.notes if n[0] == what]

    def items(self, what):
        return [n[1] for n in self.notes if n[0] == what]

    def read(self):
        """What `{"query": "stream"}` answers."""
        if not self.opened:
            return {"error": "stream_must_exist"}
        return {"stream_id": self.id, "proof_revision_url": self.url, "opener_id": self.opener,
                "closed": self.closed,
                "changes": self.pairs("change", "from_revision_url"),
                "harnesses": self.pairs("harness", "harness_revision_url"),
                "developers": self.pairs("developer", "developer_id"),
                "branches": self.pairs("branch", "branch_revision_url"),
                "pushed": self.pairs("pushed", "pushed_revision_url"),
                "pulled": self.items("pulled"),
                "reviewers": self.pairs("reviewer", "reviewer_id"),
                "reviewed": self.pairs("reviewed", "reviewed_revision_url"),
                "merged": self.pairs("merged", "merged_revision_url"),
                "abandoned": self.items("abandoned")}


# -- the layer's rules, in the engine's order (Layer.lean `rules`) ----------------------------------------------------
# Each: (reason, the commands it is tried on, holds(stream, actor, command, fields) -> bool).

def _k(f):
    return f["change_id"]


RULES = [
    ("only_opener_can_create", ("change.create",), lambda s, a, c, f: s.opener == a),
    ("change_id_must_be_new", ("change.create",), lambda s, a, c, f: not s.noted("change", _k(f))),
    ("change_must_exist", ("change.branch", "change.push", "change.pull", "change.review", "change.merge",
                           "change.abandon"), lambda s, a, c, f: s.noted("change", _k(f))),
    ("revisions_must_be_unique", ("change.branch", "change.push", "change.review", "change.merge"),
     lambda s, a, c, f: not s.revision_named(_k(f), f[REVISION_FIELD[c]])),
    ("only_opener_can_branch", ("change.branch",), lambda s, a, c, f: s.opener == a),
    ("developer_must_not_be_the_opener", ("change.branch",), lambda s, a, c, f: s.opener != f["developer_id"]),
    ("developer_is_branched_once", ("change.branch",),
     lambda s, a, c, f: not s.contains(("developer", _k(f), f["developer_id"]))),
    ("developer_must_not_be_a_reviewer", ("change.branch",),
     lambda s, a, c, f: not s.contains(("reviewer", _k(f), f["developer_id"]))),
    ("change_must_not_be_pulled", ("change.branch", "change.push"), lambda s, a, c, f: not s.noted("pulled", _k(f))),
    ("only_branched_developers_can_push", ("change.push",), lambda s, a, c, f: s.contains(("developer", _k(f), a))),
    ("only_opener_can_pull", ("change.pull",), lambda s, a, c, f: s.opener == a),
    ("change_is_pulled_once", ("change.pull",), lambda s, a, c, f: not s.noted("pulled", _k(f))),
    ("reviewer_must_not_be_a_developer", ("change.review",), lambda s, a, c, f: not s.contains(("developer", _k(f), a))),
    ("reviewer_must_not_be_the_opener", ("change.review",), lambda s, a, c, f: s.opener != a),
    ("only_opener_can_decide", ("change.merge", "change.abandon"), lambda s, a, c, f: s.opener == a),
    ("change_is_decided_once", ("change.merge", "change.abandon"), lambda s, a, c, f: not s.decided(_k(f))),
    ("change_must_be_undecided", ("change.branch", "change.push", "change.pull", "change.review"),
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
    name, k = event["event"], event.get("change_id")
    if name == "change.created":
        harness = event.get("harness_revision_url")
        return [("change", k, event["from_revision_url"])] + ([("harness", k, harness)] if harness is not None else [])
    if name == "change.branched":
        return [("developer", k, event["developer_id"]), ("branch", k, event["branch_revision_url"])]
    if name == "change.pushed":
        return [("pushed", k, event["pushed_revision_url"])]
    if name == "change.pulled":
        return [("pulled", k, "")]
    if name == "change.reviewed":
        return [("reviewer", k, event["actor_id"]), ("reviewed", k, event["reviewed_revision_url"])]
    if name == "change.merged":
        return [("merged", k, event["merged_revision_url"])]
    if name == "change.abandoned":
        return [("abandoned", k, "")]
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
