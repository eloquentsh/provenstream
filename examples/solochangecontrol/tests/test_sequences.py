# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Random command sequences against the compiled solochangecontrol engine (Hypothesis, stateful).

Three things are checked on every step of every generated sequence:

1. the engine's answer is the model's: a Python restatement of the core's admission and the layer's seventeen rules,
   tried in the engine's order, predicts the reason of every refusal, the event of every acceptance, the position
   `at`, and the host-level `malformed` for an ill-formed field;
2. the theorems hold of the accepted log as invariants: who creates, branches, pulls and decides; who pushes; the
   roles disjoint; the revisions of a change distinct; nothing branched or pushed after the pull; nothing after a
   decision; each step once;
3. `the_creator_can_always_merge`, exercised rather than observed: a rule picks an undecided change and a revision
   not yet named on it and asserts the opener's merge is accepted, whatever the sequence did before.

The read of the stream (`{"query": "stream"}`) is compared with the model's notes after every step.

Run from the repository root, with the engine built (`lake build` in examples/solochangecontrol):

    PYTHONPATH=host python3 -m pytest examples/solochangecontrol/tests -q
"""
from __future__ import annotations
import os, sys, uuid

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(REPO, "host"))

from hypothesis import HealthCheck, settings, strategies as st
from hypothesis.stateful import RuleBasedStateMachine, invariant, precondition, rule

from provenstream.engine import Engine

ENGINE = os.path.join(REPO, "examples", "solochangecontrol", ".lake", "build", "bin", "solochangecontrol-engine")
NS = uuid.UUID("12345678-1234-5678-1234-567812345678")


def U(name: str) -> str:
    return str(uuid.uuid5(NS, name))


ANN, BEN, CY, DEE, EVE, FAY = (U(p) for p in ("ann", "ben", "cy", "dee", "eve", "fay"))
PRINCIPALS = [ANN, BEN, CY, DEE, EVE, FAY]
S, T = U("stream-s"), U("stream-t")
STREAMS = [S, T]
CHANGES = [U("change-%d" % i) for i in range(4)]
PROOF_URL = "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol"
GOOD_URLS = ["https://example.org/repo/commit/%s" % x for x in
             ("r0", "r1", "b1", "b2", "b3", "b4", "c1", "c2", "c3", "c4", "c5", "m1", "m2", "m3")]
BAD_URLS = ["", "no-scheme", "https://", "://host", "https://a b/c", "https://x/\x01y", "a://b://c"]
SCREENS = ["https://example.org/screens/s%d" % i for i in range(3)]

LAYER = ("change.create", "change.branch", "change.push", "change.pull", "change.review", "change.merge",
         "change.abandon")
EVENT_OF = {"stream.open": "stream.opened", "stream.close": "stream.closed", "change.create": "change.created",
            "change.branch": "change.branched", "change.push": "change.pushed", "change.pull": "change.pulled",
            "change.review": "change.reviewed", "change.merge": "change.merged", "change.abandon": "change.abandoned"}
REVISION_NOTES = ("change", "branch", "pushed", "reviewed", "merged")

principals = st.sampled_from(PRINCIPALS)
changes = st.sampled_from(CHANGES)
urls = st.one_of(st.sampled_from(GOOD_URLS), st.sampled_from(GOOD_URLS), st.sampled_from(GOOD_URLS),
                 st.sampled_from(BAD_URLS))
screens = st.sampled_from(SCREENS)
metas = st.one_of(st.none(), st.text(alphabet=st.characters(min_codepoint=32, max_codepoint=0x7e), max_size=12))


def valid_url(s: str) -> bool:
    if len(s) > 2048 or any(not (32 < ord(c) and ord(c) != 127) for c in s):
        return False
    parts = s.split("://")
    return len(parts) == 2 and bool(parts[0]) and bool(parts[1])


def valid_meta(m) -> bool:
    return m is None or (len(m.encode()) <= 4096 and all(32 <= ord(c) and ord(c) != 127 for c in m))


class Stream:
    """The model of one stream: the core's view of it, the layer's notes, and the accepted events."""

    def __init__(self, sid: str):
        self.id = sid
        self.opened = False
        self.closed = False
        self.opener = None
        self.notes = []       # (what, change_id, who_or_revision)
        self.events = []      # accepted events, core and layer, in order (dicts as the engine returns them)

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

    def pairs(self, what, who):
        return [{"change_id": n[1], who: n[2]} for n in self.notes if n[0] == what]

    def items(self, what):
        return [n[1] for n in self.notes if n[0] == what]

    def read(self):
        if not self.opened:
            return {"error": "stream_must_exist"}
        return {"stream_id": self.id, "proof_revision_url": PROOF_URL, "opener_id": self.opener,
                "closed": self.closed,
                "changes": self.pairs("change", "from_revision_url"),
                "developers": self.pairs("developer", "developer_id"),
                "branches": self.pairs("branch", "branch_revision_url"),
                "pushed": self.pairs("pushed", "pushed_revision_url"),
                "pulled": self.items("pulled"),
                "reviewers": self.pairs("reviewer", "reviewer_id"),
                "reviewed": self.pairs("reviewed", "reviewed_revision_url"),
                "merged": self.pairs("merged", "merged_revision_url"),
                "abandoned": self.items("abandoned")}


def judge(stream: Stream, actor: str, cmd: str, f: dict, fresh: list):
    """The reason the engine refuses, 'malformed' for a request the host would not even decode, or None."""
    for key in ("from_revision_url", "branch_revision_url", "pushed_revision_url", "reviewed_revision_url",
                "merged_revision_url", "screen_url"):
        if key in f and not valid_url(f[key]):
            return "malformed"
    if not valid_meta(f.get("meta")):
        return "malformed"
    if cmd == "stream.open":
        if len(fresh) != 1:
            return "fresh_ids_must_match_the_command"
        if stream.opened:
            return "stream_id_must_be_new"
        return None
    if fresh:
        return "fresh_ids_must_match_the_command"
    if not stream.opened:
        return "stream_must_exist"
    if stream.closed:
        return "stream_must_be_open"
    if cmd == "stream.close":
        return None if actor == stream.opener else "only_opener_can_close"
    k = f["change_id"]
    opener = actor == stream.opener
    if cmd == "change.create":
        if not opener:
            return "only_opener_can_create"
        if stream.noted("change", k):
            return "change_id_must_be_new"
        return None
    if not stream.noted("change", k):
        return "change_must_exist"
    if cmd == "change.branch":
        d, u = f["developer_id"], f["branch_revision_url"]
        if stream.revision_named(k, u):
            return "revisions_must_be_unique"
        if not opener:
            return "only_opener_can_branch"
        if d == stream.opener:
            return "developer_must_not_be_the_opener"
        if stream.contains(("developer", k, d)):
            return "developer_is_branched_once"
        if stream.contains(("reviewer", k, d)):
            return "developer_must_not_be_a_reviewer"
        if stream.noted("pulled", k):
            return "change_must_not_be_pulled"
        if stream.decided(k):
            return "change_must_be_undecided"
        return None
    if cmd == "change.push":
        if stream.revision_named(k, f["pushed_revision_url"]):
            return "revisions_must_be_unique"
        if stream.noted("pulled", k):
            return "change_must_not_be_pulled"
        if not stream.contains(("developer", k, actor)):
            return "only_branched_developers_can_push"
        if stream.decided(k):
            return "change_must_be_undecided"
        return None
    if cmd == "change.pull":
        if not opener:
            return "only_opener_can_pull"
        if stream.noted("pulled", k):
            return "change_is_pulled_once"
        if stream.decided(k):
            return "change_must_be_undecided"
        return None
    if cmd == "change.review":
        if stream.revision_named(k, f["reviewed_revision_url"]):
            return "revisions_must_be_unique"
        if stream.contains(("developer", k, actor)):
            return "reviewer_must_not_be_a_developer"
        if actor == stream.opener:
            return "reviewer_must_not_be_the_opener"
        if stream.decided(k):
            return "change_must_be_undecided"
        return None
    if cmd == "change.merge":
        if stream.revision_named(k, f["merged_revision_url"]):
            return "revisions_must_be_unique"
        if not opener:
            return "only_opener_can_decide"
        if stream.decided(k):
            return "change_is_decided_once"
        return None
    if cmd == "change.abandon":
        if not opener:
            return "only_opener_can_decide"
        if stream.decided(k):
            return "change_is_decided_once"
        return None
    raise AssertionError(cmd)


def notes_of(cmd: str, actor: str, f: dict):
    k = f.get("change_id")
    if cmd == "change.create":
        return [("change", k, f["from_revision_url"])]
    if cmd == "change.branch":
        return [("developer", k, f["developer_id"]), ("branch", k, f["branch_revision_url"])]
    if cmd == "change.push":
        return [("pushed", k, f["pushed_revision_url"])]
    if cmd == "change.pull":
        return [("pulled", k, "")]
    if cmd == "change.review":
        return [("reviewer", k, actor), ("reviewed", k, f["reviewed_revision_url"])]
    if cmd == "change.merge":
        return [("merged", k, f["merged_revision_url"])]
    if cmd == "change.abandon":
        return [("abandoned", k, "")]
    return []


class SoloChangeControl(RuleBasedStateMachine):
    def __init__(self):
        super().__init__()
        self.engine = Engine([ENGINE])
        self.engine.start()
        self.streams = {sid: Stream(sid) for sid in STREAMS}
        self.steps = 0
        self.fresh_counter = 0

    def teardown(self):
        self.engine.stop()

    # ---- one request: the engine against the model ----

    def send(self, actor: str, cmd: str, f: dict, fresh=None):
        fresh = fresh if fresh is not None else []
        sid = f["stream_id"]
        stream = self.streams[sid]
        want = judge(stream, actor, cmd, f, fresh)
        req = {"actor_id": actor, "command": dict(command=cmd, **f), "fresh": fresh}
        got = self.engine.decide(req)
        self.steps += 1
        if want == "malformed":
            assert got.get("error") == "malformed", (req, got)
            return got
        assert "error" not in got, (req, got)
        assert got["stream_id"] == sid and got["at"] == len(stream.events), (req, got, len(stream.events))
        if want is not None:
            assert got["accept"] is False and got["reason"] == want, (req, got, want)
            return got
        assert got["accept"] is True, (req, got, "model accepts")
        expect = {"event": EVENT_OF[cmd], "stream_id": sid, "actor_id": actor, "meta": f.get("meta")}
        expect.update({k: v for k, v in f.items() if k not in ("stream_id", "meta")})
        assert got["event"] == expect, (got["event"], expect)
        # apply to the model
        if cmd == "stream.open":
            stream.opened, stream.opener = True, actor
        elif cmd == "stream.close":
            stream.closed = True
        stream.notes.extend(notes_of(cmd, actor, f))
        stream.events.append(got["event"])
        return got

    # ---- the core ----

    @rule(actor=principals, sid=st.sampled_from(STREAMS), meta=metas, wrong_fresh=st.booleans())
    def open_stream(self, actor, sid, meta, wrong_fresh):
        f = {"stream_id": sid, "proof_revision_url": PROOF_URL}
        if meta is not None:
            f["meta"] = meta
        fresh = [] if wrong_fresh else [sid]
        # the engine's request has no stream_id field on an open: it mints it
        stream = self.streams[sid]
        want = judge(stream, actor, "stream.open", f, fresh)
        req = {"actor_id": actor, "command": {"command": "stream.open", "proof_revision_url": PROOF_URL,
                                              **({"meta": meta} if meta is not None else {})}, "fresh": fresh}
        got = self.engine.decide(req)
        self.steps += 1
        if want is not None:
            assert got["accept"] is False and got["reason"] == want, (req, got, want)
            return
        assert got["accept"] is True and got["at"] == 0 and got["stream_id"] == sid, (req, got)
        assert got["event"] == {"event": "stream.opened", "stream_id": sid, "actor_id": actor, "meta": meta,
                                "proof_revision_url": PROOF_URL}, got["event"]
        stream.opened, stream.opener = True, actor
        stream.events.append(got["event"])

    @precondition(lambda self: self.steps > 12)
    @rule(actor=principals, sid=st.sampled_from(STREAMS), meta=metas)
    def close_stream(self, actor, sid, meta):
        f = {"stream_id": sid}
        if meta is not None:
            f["meta"] = meta
        self.send(actor, "stream.close", f)

    # ---- the layer ----

    @rule(actor=principals, sid=st.sampled_from(STREAMS), k=changes, u=urls, meta=metas,
          wrong_fresh=st.sampled_from([False] * 9 + [True]))
    def create(self, actor, sid, k, u, meta, wrong_fresh):
        f = {"stream_id": sid, "change_id": k, "from_revision_url": u}
        if meta is not None:
            f["meta"] = meta
        self.send(actor, "change.create", f, [U("extra")] if wrong_fresh else [])

    @rule(actor=principals, sid=st.sampled_from(STREAMS), k=changes, d=principals, u=urls, meta=metas)
    def branch(self, actor, sid, k, d, u, meta):
        f = {"stream_id": sid, "change_id": k, "developer_id": d, "branch_revision_url": u}
        if meta is not None:
            f["meta"] = meta
        self.send(actor, "change.branch", f)

    @rule(actor=principals, sid=st.sampled_from(STREAMS), k=changes, u=urls, meta=metas)
    def push(self, actor, sid, k, u, meta):
        f = {"stream_id": sid, "change_id": k, "pushed_revision_url": u}
        if meta is not None:
            f["meta"] = meta
        self.send(actor, "change.push", f)

    @rule(actor=principals, sid=st.sampled_from(STREAMS), k=changes, meta=metas)
    def pull(self, actor, sid, k, meta):
        f = {"stream_id": sid, "change_id": k}
        if meta is not None:
            f["meta"] = meta
        self.send(actor, "change.pull", f)

    @rule(actor=principals, sid=st.sampled_from(STREAMS), k=changes, u=urls, sc=st.one_of(screens, urls), meta=metas)
    def review(self, actor, sid, k, u, sc, meta):
        f = {"stream_id": sid, "change_id": k, "reviewed_revision_url": u, "screen_url": sc}
        if meta is not None:
            f["meta"] = meta
        self.send(actor, "change.review", f)

    @rule(actor=principals, sid=st.sampled_from(STREAMS), k=changes, u=urls, meta=metas)
    def merge(self, actor, sid, k, u, meta):
        f = {"stream_id": sid, "change_id": k, "merged_revision_url": u}
        if meta is not None:
            f["meta"] = meta
        self.send(actor, "change.merge", f)

    @rule(actor=principals, sid=st.sampled_from(STREAMS), k=changes, meta=metas)
    def abandon(self, actor, sid, k, meta):
        f = {"stream_id": sid, "change_id": k}
        if meta is not None:
            f["meta"] = meta
        self.send(actor, "change.abandon", f)

    # ---- the acceptance theorem, exercised ----

    def undecided(self):
        return [(s, k) for s in self.streams.values() if s.opened and not s.closed
                for k in CHANGES if s.noted("change", k) and not s.decided(k)]

    @precondition(lambda self: bool(self.undecided()))
    @rule(data=st.data())
    def the_creator_can_always_merge(self, data):
        """Whatever happened before: an undecided change on an open stream, a revision not yet named on it, the
        opener's merge is accepted."""
        stream, k = data.draw(st.sampled_from(self.undecided()))
        free = [u for u in GOOD_URLS if not stream.revision_named(k, u)]
        if free:
            u = data.draw(st.sampled_from(free))
        else:
            self.fresh_counter += 1
            u = "https://example.org/repo/commit/fresh%d" % self.fresh_counter
        got = self.send(stream.opener, "change.merge", {"stream_id": stream.id, "change_id": k,
                                                        "merged_revision_url": u})
        assert got["accept"] is True, ("the_creator_can_always_merge", got)

    # ---- the theorems, as invariants of the accepted log ----

    @invariant()
    def theorems_hold(self):
        for s in self.streams.values():
            if not s.opened:
                assert not s.events
                continue
            opener = s.opener
            created, developers, reviewers, pulled, decided = set(), {}, {}, set(), set()
            revisions = {}
            for e in s.events:
                name = e["event"]
                if name in ("stream.opened", "stream.closed"):
                    if name == "stream.closed":
                        assert e["actor_id"] == opener, "only_the_opener_closes_the_stream"
                        assert e is s.events[-1], "nothing_follows_a_close"
                    continue
                k = e["change_id"]
                if name != "change.created":
                    assert k in created, "every_event_names_a_created_change"
                assert k not in decided, "nothing_follows_a_decision"
                rev = {"change.created": "from_revision_url", "change.branched": "branch_revision_url",
                       "change.pushed": "pushed_revision_url", "change.reviewed": "reviewed_revision_url",
                       "change.merged": "merged_revision_url"}.get(name)
                if rev:
                    assert e[rev] not in revisions.setdefault(k, set()), "revisions_are_distinct"
                    revisions[k].add(e[rev])
                if name == "change.created":
                    assert e["actor_id"] == opener, "every_change_is_created_by_the_opener"
                    assert k not in created, "a_change_is_created_once"
                    created.add(k)
                elif name == "change.branched":
                    d = e["developer_id"]
                    assert e["actor_id"] == opener, "every_branch_is_by_the_opener"
                    assert d != opener, "no_developer_is_the_opener"
                    assert d not in developers.setdefault(k, set()), "a_developer_is_branched_once"
                    assert d not in reviewers.get(k, set()), "no_developer_is_a_reviewer"
                    assert k not in pulled, "nothing_is_branched_or_pushed_after_the_pull"
                    developers[k].add(d)
                elif name == "change.pushed":
                    assert e["actor_id"] in developers.get(k, set()), "every_push_is_by_a_branched_developer"
                    assert k not in pulled, "nothing_is_branched_or_pushed_after_the_pull"
                elif name == "change.pulled":
                    assert e["actor_id"] == opener, "the_pull_is_by_the_opener"
                    assert k not in pulled, "a_change_is_pulled_once"
                    pulled.add(k)
                elif name == "change.reviewed":
                    r = e["actor_id"]
                    assert r != opener, "no_reviewer_is_the_opener"
                    assert r not in developers.get(k, set()), "no_developer_is_a_reviewer"
                    reviewers.setdefault(k, set()).add(r)
                elif name in ("change.merged", "change.abandoned"):
                    assert e["actor_id"] == opener, "the_merge_is_by_the_opener / the_abandon_is_by_the_opener"
                    assert k not in decided, "a_change_is_decided_once"
                    decided.add(k)
                else:
                    raise AssertionError(name)
            for k in created:
                assert not (developers.get(k, set()) & reviewers.get(k, set())), "roles_are_disjoint"

    @invariant()
    def read_is_the_notes(self):
        for s in self.streams.values():
            got = self.engine.query({"query": "stream", "stream_id": s.id})
            assert got == s.read(), (got, s.read())


TestSoloChangeControl = SoloChangeControl.TestCase
TestSoloChangeControl.settings = settings(max_examples=120, stateful_step_count=50, deadline=None, database=None,
                                          suppress_health_check=[HealthCheck.too_slow])
