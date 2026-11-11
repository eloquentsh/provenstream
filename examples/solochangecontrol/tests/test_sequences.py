# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Random command sequences against the compiled solochangecontrol engine (Hypothesis, stateful), with requirements on
what the run must have exercised, so that a pass means something measurable.

On every step of every generated sequence:

1. the engine's answer is the model's (solo_model.py: the wire's decoding, the core's admission and the layer's
   seventeen rules in the engine's order): the reason of every refusal, the event and position of every acceptance,
   `malformed` for a request the engine does not decode;
2. the theorems of SoloChangeControl/Theorems.lean hold of the accepted log as invariants;
3. `the_creator_can_always_merge` holds right here: for every undecided change on an open stream the engine's state is
   snapshotted, the opener's merge at a revision not yet named is sent and must be accepted, and the snapshot is loaded
   back, after which the stream reads as before;
4. the read of each stream (`{"query": "stream"}`) is the model's notes.

At the end of the run (test_coverage_is_complete, test_deep_states_are_reached) the run must have observed, for every
command the engine describes, every (command, rule) refusal the description lists, an acceptance, and a malformed
request; a wrong number of fresh ids; the acceptance theorem exercised as a rule; and each named deep state of
DEEP_STATES at least once. The counters are printed at exit.

Run from the repository root, with the engine built (`lake build` in examples/solochangecontrol):

    PYTHONPATH=host python3 -m pytest examples/solochangecontrol/tests -q

SOLO_EXAMPLES and SOLO_STEPS set the budget (default 400 x 80). SOLO_ENGINE names another engine (the mutant script
does). SOLO_RECORD=1 restricts the run to four principals, derandomizes it and writes the best passing sequences as
conformance cases to cases/solochangecontrol.jsonl (record.py). A failing sequence is written to .hypothesis/ in both
forms, shrunk.
"""
from __future__ import annotations
import atexit, collections, os, sys, uuid

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(REPO, "host"))
sys.path.insert(0, HERE)

import pytest
from hypothesis import HealthCheck, settings, strategies as st
from hypothesis.stateful import RuleBasedStateMachine, initialize, invariant, precondition, rule

from provenstream.engine import Engine
import solo_model as M
import record

ENGINE = os.environ.get("SOLO_ENGINE") or os.path.join(REPO, "examples", "solochangecontrol", ".lake", "build", "bin",
                                                        "solochangecontrol-engine")
RECORDING = bool(os.environ.get("SOLO_RECORD"))
DUMP_DIR = os.environ.get("SOLO_DUMP") or os.path.join(HERE, ".hypothesis")
CASES_PATH = os.path.join(HERE, "cases", "solochangecontrol.jsonl")
NS = uuid.UUID("12345678-1234-5678-1234-567812345678")


def U(name: str) -> str:
    return str(uuid.uuid5(NS, name))


ANN, BEN, CY, DEE, EVE, FAY = (U(p) for p in ("ann", "ben", "cy", "dee", "eve", "fay"))
PRINCIPALS = [ANN, BEN, CY, DEE] if RECORDING else [ANN, BEN, CY, DEE, EVE, FAY]
S, T = U("stream-s"), U("stream-t")
STREAMS = [S, T]
CHANGES = [U("change-%d" % i) for i in range(4)]
PROOF_URL = M.PROOF_URL
GOOD_URLS = ["https://example.org/repo/commit/%s" % x for x in
             ("r0", "r1", "b1", "b2", "b3", "b4", "c1", "c2", "c3", "c4", "c5", "m1", "m2", "m3")]
BAD_URLS = ["", "no-scheme", "https://", "://host", "https://a b/c", "https://x/\x01y", "a://b://c"]
BAD_PROOF_URLS = ["https://example.org/provenstream/commit/0123456789abcdef", PROOF_URL.upper(),
                  "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567",
                  "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/../x",
                  "https://example.org/commit/0123456789abcdef0123456789abcdef01234567", "ftp:/x/commit/" + "0" * 40]
SCREENS = ["https://example.org/screens/s%d" % i for i in range(3)]
HARNESSES = ["https://example.org/harness/commit/h%d" % i for i in range(3)]

# -- what the run exercised: printed at exit, required by the tests at the end of this file -----------------------------

SEEN = collections.Counter()      # (command, outcome): outcome is 'accepted', a reason, or 'malformed'
EXTRA = collections.Counter()     # the acceptance theorem as a rule and as a probe, per step
DEEP = collections.Counter()      # deep state -> runs that reached it
RUNS = collections.Counter()      # runs, steps, requests
PASSING = []                      # (score, name, trace) of passing runs, when recording

# every refusal the engine describes, per command; what aimed_refusal aims at and test_coverage_is_complete requires
TARGETS = [(cmd, r) for cmd in M.COMMANDS for r in M.expected_rules(cmd)] + \
          [(cmd, "malformed") for cmd in M.COMMANDS] + \
          [("stream.open", "fresh_ids_must_match_the_command"), ("change.create", "fresh_ids_must_match_the_command")]

# every pair of layer rules tried on one command, in the engine's order: (command, first, second)
PAIR_TARGETS = [(cmd, a, b) for cmd in M.LAYER for i, a in enumerate(M.rules_of(cmd)) for b in M.rules_of(cmd)[i + 1:]]

DEEP_STATES = ("a merge after at least one review", "a review before the pull and a review after it",
               "two distinct reviewers on one change", "pushes by two developers on one change",
               "a change created from another change's merged revision", "a close while a change is undecided",
               "both streams open at once")


@atexit.register
def _report():
    if not SEEN:
        return
    print("\nsolochangecontrol sequences: %d runs, %d steps, %d requests" % (RUNS["runs"], RUNS["steps"],
                                                                            RUNS["requests"]), file=sys.stderr)
    width = max(len("%s %s" % k) for k in SEEN)
    for (cmd, outcome), n in sorted(SEEN.items(), key=lambda kv: (kv[0][0], -kv[1], kv[0][1])):
        print("  %-*s %7d" % (width, "%s %s" % (cmd, outcome), n), file=sys.stderr)
    for k, n in sorted(EXTRA.items()):
        print("  %-*s %7d" % (width, k, n), file=sys.stderr)
    print("deep states reached (runs):", file=sys.stderr)
    for name in DEEP_STATES:
        print("  %-*s %7d" % (width, name, DEEP[name]), file=sys.stderr)


principals = st.sampled_from(PRINCIPALS)
changes = st.sampled_from(CHANGES)
metas = st.one_of(st.none(), st.text(alphabet=st.characters(min_codepoint=32, max_codepoint=0x7e), max_size=12))


def deep_states(streams) -> set:
    """The named deep states a run's accepted log reached."""
    reached = set()
    both = False
    for s in streams.values():
        if not s.opened:
            continue
        by_change = collections.defaultdict(list)
        merged_revisions = {}
        for e in s.events:
            if "change_id" in e:
                by_change[e["change_id"]].append(e)
            if e["event"] == "change.merged":
                merged_revisions[e["merged_revision_url"]] = e["change_id"]
            if e["event"] == "change.created" and e["from_revision_url"] in merged_revisions and \
                    merged_revisions[e["from_revision_url"]] != e["change_id"]:
                reached.add("a change created from another change's merged revision")
        for k, evs in by_change.items():
            names = [e["event"] for e in evs]
            if "change.reviewed" in names and "change.merged" in names and \
                    names.index("change.reviewed") < names.index("change.merged"):
                reached.add("a merge after at least one review")
            if "change.pulled" in names:
                p = names.index("change.pulled")
                if "change.reviewed" in names[:p] and "change.reviewed" in names[p:]:
                    reached.add("a review before the pull and a review after it")
            if len({e["actor_id"] for e in evs if e["event"] == "change.reviewed"}) >= 2:
                reached.add("two distinct reviewers on one change")
            if len({e["actor_id"] for e in evs if e["event"] == "change.pushed"}) >= 2:
                reached.add("pushes by two developers on one change")
        if s.closed and s.undecided():
            reached.add("a close while a change is undecided")
        both = both or getattr(s, "opened_while_other_open", False)
    if both:
        reached.add("both streams open at once")
    return reached


class SoloChangeControl(RuleBasedStateMachine):
    def __init__(self):
        super().__init__()
        self.engine = Engine([ENGINE])
        self.engine.start()
        self.model = M.Model()
        for sid in STREAMS:
            self.model.stream(sid)
        self.steps = 0
        self.fresh_counter = 0
        self.trace = []
        self.failure = None

    @property
    def streams(self):
        return self.model.streams

    def teardown(self):
        self.engine.stop()
        RUNS["runs"] += 1
        RUNS["steps"] += self.steps
        if self.failure is not None:
            if self.trace:
                self.trace[-1]["failed"] = True
            record.dump_failing(self.trace, self.failure, DUMP_DIR)
            return
        reached = deep_states(self.streams)
        for name in reached:
            DEEP[name] += 1
        if RECORDING:
            accepted = sum(1 for t in self.trace if not t.get("probe") and t["want"] is None)
            PASSING.append((len(reached) * 100 + accepted, "run%03d" % RUNS["runs"],
                            [t for t in self.trace if not t.get("probe")]))

    def fail(self, *why):
        self.failure = why
        raise AssertionError(why)

    def check(self, cond, *why):
        if not cond:
            self.fail(*why)

    # ---- one request: the engine against the model ----

    def send(self, actor: str, cmd: dict, fresh=None):
        """`cmd` is the command object (with its `command` key). The model predicts; the engine answers; they agree."""
        req = {"actor_id": actor, "command": cmd, "fresh": list(fresh or [])}
        want, sid, at, event = self.model.step(req)
        got = self.engine.decide(req)
        self.steps += 1
        RUNS["requests"] += 1
        name = cmd.get("command") if isinstance(cmd, dict) else None
        SEEN[(name, "accepted" if want is None else want)] += 1
        self.trace.append({"request": req, "answer": got, "want": want})
        if want == "malformed":
            self.check(got.get("error") == "malformed", "the model says malformed", req, got)
            return got
        self.check("error" not in got, "the engine says malformed, the model does not", req, got)
        self.check(got["stream_id"] == sid and got["at"] == at, "stream or position", req, got, sid, at)
        if want is not None:
            self.check(got["accept"] is False and got["reason"] == want, "the reason", req, got, want)
            return got
        self.check(got["accept"] is True, "the model accepts", req, got)
        self.check(got["event"] == event, "the event", got["event"], event)
        return got

    # ---- choosing, biased towards the valid, with the invalid kept in ----

    def pick_stream(self, data):
        return data.draw(st.sampled_from([S] * 4 + [T]))

    def pick_actor(self, data, stream, prefer):
        """`prefer`: 'opener', ('developer', k), ('reviewer', k) (a principal who is neither a developer nor the
        opener), or None for anyone. Four times in five the preferred, else anyone."""
        if stream.opener is not None and prefer is not None and data.draw(st.sampled_from([True] * 4 + [False])):
            if prefer == "opener":
                return stream.opener
            k = prefer[1]
            devs = stream.developers(k)
            if prefer[0] == "developer" and devs:
                return data.draw(st.sampled_from(devs))
            if prefer[0] == "reviewer":
                return self.pick_reviewer(data, stream, k)
        return data.draw(principals)

    def pick_change(self, data, stream, prefer_undecided=True, ripe=None):
        """Half the time a change `ripe` for the rule (one step from a deep state), else mostly a live one, else any."""
        created = stream.changes()
        if prefer_undecided:
            live = stream.undecided()
            if ripe is not None and live and data.draw(st.booleans()):
                good = [k for k in live if ripe(k)]
                if good:
                    return data.draw(st.sampled_from(good))
            if live and data.draw(st.sampled_from([True] * 5 + [False])):
                return data.draw(st.sampled_from(live))
        if created and data.draw(st.sampled_from([True] * 3 + [False])):
            return data.draw(st.sampled_from(created))
        return data.draw(changes)

    def pick_url(self, data, stream, k, continuing=False):
        """Mostly a revision not yet named on the change; sometimes one that is; one time in fourteen a bad one; for a
        create, often another change's merged revision (a continuation)."""
        roll = data.draw(st.integers(0, 13))
        if roll == 0:
            return data.draw(st.sampled_from(BAD_URLS))
        used = stream.revisions(k)
        if roll == 1 and used:
            return data.draw(st.sampled_from(used))
        if continuing and roll in (2, 3, 4):
            merged = [n[2] for n in stream.notes if n[0] == "merged" and n[1] != k]
            if merged:
                return data.draw(st.sampled_from(merged))
        free = [u for u in GOOD_URLS if u not in used]
        if free:
            return data.draw(st.sampled_from(free))
        self.fresh_counter += 1
        return "https://example.org/repo/commit/fresh%d" % self.fresh_counter

    def with_meta(self, data, f):
        m = data.draw(metas)
        if m is not None:
            f["meta"] = m
        if data.draw(st.integers(0, 59)) == 0:
            f["meta"] = data.draw(st.sampled_from(["a\tb", "x\x00y", "\x7f", "é" * 2048 + "a"]))
        return f

    def mangle(self, data, f, always=False):
        """One time in forty (or when asked), a command the engine will not decode: an id not in canonical form, an
        unknown key, a required field missing."""
        if not always and data.draw(st.integers(0, 39)) != 0:
            return f
        how = data.draw(st.sampled_from(["upper", "extra", "missing"]))
        uuids = [k for k, v in f.items() if k != "command" and M.valid_uuid(v) and any(c.isalpha() for c in v)]
        required = [k for k in f if k not in ("command", "meta", "harness_revision_url")]
        if how == "upper" and uuids:
            k = data.draw(st.sampled_from(uuids))
            f[k] = f[k].upper()
        elif how == "missing" and required:
            del f[data.draw(st.sampled_from(required))]
        else:
            f["extra"] = 1
        return f

    def life(self, stream, k):
        """How many events the change has: decisions are held back on a young change so that work accumulates."""
        return sum(1 for e in stream.events if e.get("change_id") == k)

    def fresh_developer(self, stream, k):
        return [p for p in PRINCIPALS if p != stream.opener and p not in stream.developers(k)
                and p not in stream.reviewers(k)]

    def pick_developer(self, data, stream, k):
        """Five times in eight someone the opener may branch (not the opener, not yet a developer or reviewer of k);
        else, deliberately, the opener, a developer already branched, or a reviewer of the change."""
        if stream.opener is None:
            return data.draw(principals)
        roll = data.draw(st.integers(0, 7))
        if roll == 0:
            return stream.opener
        if roll == 1 and stream.developers(k):
            return data.draw(st.sampled_from(stream.developers(k)))
        if roll == 2 and stream.reviewers(k):
            return data.draw(st.sampled_from(stream.reviewers(k)))
        fresh = self.fresh_developer(stream, k)
        return data.draw(st.sampled_from(fresh)) if fresh else data.draw(principals)

    def pick_reviewer(self, data, stream, k):
        """Someone who may review: neither the opener nor a developer of the change. Two times in three one who has
        reviewed k already, so that reviewing does not use up the principals the opener could still branch (a reviewer
        is never afterwards a developer of the change); scenario_two_reviews brings in the second reviewer."""
        able = [p for p in PRINCIPALS if p != stream.opener and p not in stream.developers(k)]
        again = [p for p in able if p in stream.reviewers(k)]
        pool = again if again and data.draw(st.sampled_from([True] * 2 + [False])) else able
        return data.draw(st.sampled_from(pool)) if pool else data.draw(principals)

    # ---- the core ----

    @initialize(data=st.data())
    def maybe_open(self, data):
        """Most runs start with S open by ann, and some with T open by ben too; some start cold, so the admission is
        tried as well."""
        if data.draw(st.sampled_from([True] * 5 + [False])):
            self.send(ANN, {"command": "stream.open", "proof_revision_url": PROOF_URL}, [S])
            if data.draw(st.sampled_from([False] * 3 + [True])):
                self.send(BEN, {"command": "stream.open", "proof_revision_url": PROOF_URL}, [T])
                self.streams[T].opened_while_other_open = True

    @rule(data=st.data())
    def open_stream(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        actor = data.draw(principals)
        url = PROOF_URL if data.draw(st.sampled_from([True] * 3 + [False])) else data.draw(st.sampled_from(BAD_PROOF_URLS))
        f = self.mangle(data, self.with_meta(data, {"command": "stream.open", "proof_revision_url": url}))
        fresh = data.draw(st.sampled_from([[sid]] * 9 + [[], [sid, U("extra")]]))
        other = self.streams[T if sid == S else S]
        other_open = other.opened and not other.closed
        got = self.send(actor, f, fresh)
        if got.get("accept") and other_open:
            stream.opened_while_other_open = True

    @precondition(lambda self: self.steps > 25)
    @rule(data=st.data())
    def close_stream(self, data):
        if data.draw(st.sampled_from([True] * 2 + [False])):
            return
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        actor = stream.opener if stream.opener and data.draw(st.sampled_from([True] * 2 + [False])) else data.draw(principals)
        self.send(actor, self.mangle(data, self.with_meta(data, {"command": "stream.close", "stream_id": sid})))

    # ---- the layer ----

    @rule(data=st.data())
    def create(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        actor = self.pick_actor(data, stream, "opener")
        k = data.draw(changes)
        f = {"command": "change.create", "stream_id": sid, "change_id": k,
             "from_revision_url": self.pick_url(data, stream, k, continuing=True)}
        # the optional harness revision: absent half the time, else null, a harness, or (one time in twelve) a bad URL
        roll = data.draw(st.integers(0, 11))
        if roll == 0:
            f["harness_revision_url"] = None
        elif roll in (1, 2, 3, 4):
            f["harness_revision_url"] = data.draw(st.sampled_from(HARNESSES))
        elif roll == 5:
            f["harness_revision_url"] = data.draw(st.sampled_from(BAD_URLS))
        fresh = [U("extra")] if data.draw(st.integers(0, 19)) == 0 else []
        self.send(actor, self.mangle(data, self.with_meta(data, f)), fresh)

    @rule(data=st.data())
    def branch(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        actor = self.pick_actor(data, stream, "opener")
        # ripe: one developer already, not pulled: a second developer can be branched
        k = self.pick_change(data, stream, ripe=lambda k: len(stream.developers(k)) == 1 and not stream.noted("pulled", k))
        d = self.pick_developer(data, stream, k)
        f = {"command": "change.branch", "stream_id": sid, "change_id": k, "developer_id": d,
             "branch_revision_url": self.pick_url(data, stream, k)}
        self.send(actor, self.mangle(data, self.with_meta(data, f)))

    @rule(data=st.data())
    def push(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        decided = [k for k in stream.changes() if stream.decided(k) and not stream.noted("pulled", k)]
        if decided and data.draw(st.integers(0, 7)) == 0:
            k = data.draw(st.sampled_from(decided))         # a push after the decision: refused
        else:
            k = self.pick_change(data, stream)
        actor = self.pick_actor(data, stream, ("developer", k))
        f = {"command": "change.push", "stream_id": sid, "change_id": k, "pushed_revision_url": self.pick_url(data, stream, k)}
        self.send(actor, self.mangle(data, self.with_meta(data, f)))

    @rule(data=st.data())
    def pull(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        actor = self.pick_actor(data, stream, "opener")
        # ripe: reviewed and not yet pulled: a review after the pull becomes possible
        k = self.pick_change(data, stream, ripe=lambda k: stream.reviewers(k) and not stream.noted("pulled", k))
        if self.life(stream, k) < 3 and data.draw(st.sampled_from([True] * 2 + [False])):
            return
        self.send(actor, self.mangle(data, self.with_meta(data, {"command": "change.pull", "stream_id": sid, "change_id": k})))

    @rule(data=st.data())
    def review(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        k = self.pick_change(data, stream)
        actor = self.pick_actor(data, stream, ("reviewer", k))
        devs = stream.developers(k)
        if devs and data.draw(st.sampled_from([False] * 7 + [True])):
            actor = data.draw(st.sampled_from(devs))            # a developer reviewing its own change: refused
        sc = data.draw(st.sampled_from(SCREENS * 4 + BAD_URLS[:1]))
        f = {"command": "change.review", "stream_id": sid, "change_id": k,
             "reviewed_revision_url": self.pick_url(data, stream, k), "screen_url": sc}
        self.send(actor, self.mangle(data, self.with_meta(data, f)))

    @rule(data=st.data())
    def merge(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        actor = self.pick_actor(data, stream, "opener")
        k = self.pick_change(data, stream, prefer_undecided=False)
        hold = 5 if self.life(stream, k) < 8 else 1
        if data.draw(st.sampled_from([True] * hold + [False])):
            return
        f = {"command": "change.merge", "stream_id": sid, "change_id": k, "merged_revision_url": self.pick_url(data, stream, k)}
        self.send(actor, self.mangle(data, self.with_meta(data, f)))

    @rule(data=st.data())
    def abandon(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        actor = self.pick_actor(data, stream, "opener")
        k = self.pick_change(data, stream, prefer_undecided=False)
        hold = 7 if self.life(stream, k) < 8 else 1
        if data.draw(st.sampled_from([True] * hold + [False])):
            return
        self.send(actor, self.mangle(data, self.with_meta(data, {"command": "change.abandon", "stream_id": sid, "change_id": k})))

    # ---- scenarios: a few valid steps on one change in one rule, so that the deep states are reached ----
    # Every request still goes through `send`, so each is predicted by the model and checked against the engine.

    def live_change(self, data, stream, ripe):
        """An undecided change `ripe` for the scenario, else None."""
        good = [k for k in stream.undecided() if ripe(k)] if stream.opened and not stream.closed else []
        return data.draw(st.sampled_from(good)) if good else None

    def layer(self, data, actor, cmd, stream, k, **fields):
        f = {"command": cmd, "stream_id": stream.id, "change_id": k}
        f.update(fields)
        return self.send(actor, self.with_meta(data, f))

    @rule(data=st.data())
    def scenario_second_developer_pushes(self, data):
        """On a change with one developer who has pushed, the opener branches another, and both push."""
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        k = self.live_change(data, stream, lambda k: not stream.noted("pulled", k) and len(stream.developers(k)) <= 2)
        if k is None:
            return
        devs = stream.developers(k)
        if len(devs) < 2:
            fresh = self.fresh_developer(stream, k)
            if not fresh:
                return
            d = data.draw(st.sampled_from(fresh))
            self.layer(data, stream.opener, "change.branch", stream, k, developer_id=d,
                       branch_revision_url=self.unnamed(data, stream, k))
            devs = stream.developers(k)
        for d in devs[-2:]:
            self.layer(data, d, "change.push", stream, k, pushed_revision_url=self.unnamed(data, stream, k))

    @rule(data=st.data())
    def scenario_two_reviews(self, data):
        """Two distinct reviewers each publish a screen on one change."""
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        k = self.live_change(data, stream, lambda k: len(set(stream.reviewers(k))) <= 1)
        if k is None:
            return
        able = [p for p in PRINCIPALS if p != stream.opener and p not in stream.developers(k) and p not in stream.reviewers(k)]
        for r in able[:2]:
            self.layer(data, r, "change.review", stream, k, reviewed_revision_url=self.unnamed(data, stream, k),
                       screen_url=data.draw(st.sampled_from(SCREENS)))

    @rule(data=st.data())
    def scenario_pull_then_review(self, data):
        """A reviewed change is pulled by the opener, and reviewed again after the pull."""
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        k = self.live_change(data, stream, lambda k: not stream.noted("pulled", k))
        if k is None:
            return
        if not stream.reviewers(k):
            self.layer(data, self.pick_reviewer(data, stream, k), "change.review", stream, k,
                       reviewed_revision_url=self.unnamed(data, stream, k), screen_url=data.draw(st.sampled_from(SCREENS)))
        self.layer(data, stream.opener, "change.pull", stream, k)
        self.layer(data, self.pick_reviewer(data, stream, k), "change.review", stream, k,
                   reviewed_revision_url=self.unnamed(data, stream, k), screen_url=data.draw(st.sampled_from(SCREENS)))

    @rule(data=st.data())
    def scenario_review_then_merge(self, data):
        """A change with work on it is reviewed and merged, and a continuation is created from the merged revision."""
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        k = self.live_change(data, stream, lambda k: self.life(stream, k) >= 2)
        if k is None:
            return
        if not stream.reviewers(k):
            self.layer(data, self.pick_reviewer(data, stream, k), "change.review", stream, k,
                       reviewed_revision_url=self.unnamed(data, stream, k), screen_url=data.draw(st.sampled_from(SCREENS)))
        m = self.unnamed(data, stream, k)
        self.layer(data, stream.opener, "change.merge", stream, k, merged_revision_url=m)
        new = [c for c in CHANGES if not stream.noted("change", c)]
        if new and data.draw(st.sampled_from([True] * 2 + [False])):
            self.layer(data, stream.opener, "change.create", stream, data.draw(st.sampled_from(new)), from_revision_url=m)

    # ---- refusals, aimed: a request built to meet one named rule, the target drawn by Hypothesis ----
    # Each (command, reason) the engine describes is a target. The construction says how the rule is reached; the model
    # still judges the request, so a construction that misses is a refusal for another reason, or an acceptance, and
    # is checked like any other request.

    def form(self, data, cmd, stream, k=None, url=None, developer=None):
        f = {"command": cmd}
        if cmd == "stream.open":
            f["proof_revision_url"] = url or PROOF_URL
            return f
        f["stream_id"] = stream.id
        if cmd == "stream.close":
            return f
        f["change_id"] = k
        if cmd in M.REVISION_FIELD:
            f[M.REVISION_FIELD[cmd]] = url or self.unnamed(data, stream, k)
        if cmd == "change.branch":
            fresh = self.fresh_developer(stream, k)
            f["developer_id"] = developer or (data.draw(st.sampled_from(fresh)) if fresh else data.draw(principals))
        if cmd == "change.review":
            f["screen_url"] = data.draw(st.sampled_from(SCREENS))
        return f

    def aim(self, data, cmd, reason):
        """`(actor, command, fresh)` that the rules refuse for `reason`, built from the current state; None when the
        state offers no way to it."""
        def pick(xs):
            xs = list(xs)
            return data.draw(st.sampled_from(xs)) if xs else None

        streams = list(self.streams.values())
        opened = [s for s in streams if s.opened and not s.closed]
        # the open stream with undecided changes, when there is one: most targets need a change to be about
        s = pick([x for x in opened if x.undecided()] or opened) or self.streams[S]
        k0 = pick(s.changes()) or CHANGES[0]
        others = [p for p in PRINCIPALS if p != s.opener]
        if reason == "malformed":
            f = self.mangle(data, self.form(data, cmd, s, k0), always=True)
            return (data.draw(principals), f, [S] if cmd == "stream.open" else [])
        if reason == "fresh_ids_must_match_the_command":
            if cmd == "stream.open":
                return (data.draw(principals), self.form(data, cmd, s), pick([[], [s.id, U("extra")]]))
            return (s.opener or ANN, self.form(data, cmd, s, k0), [U("extra")])
        if cmd == "stream.open":
            if reason == "stream_id_must_be_new":
                t = pick(x for x in streams if x.opened)
                return (data.draw(principals), self.form(data, cmd, t), [t.id]) if t else None
            t = pick(x for x in streams if not x.opened)
            return (data.draw(principals), self.form(data, cmd, t, url=pick(BAD_PROOF_URLS)), [t.id]) if t else None
        if reason == "stream_must_be_open" and not any(x.closed for x in streams):
            spare = [x for x in opened if x is not s]                  # set up: close the other open stream first
            if spare:
                self.send(spare[0].opener, self.form(data, "stream.close", spare[0]), [])
        if reason in ("stream_must_exist", "stream_must_be_open"):
            t = pick(x for x in streams if (not x.opened if reason == "stream_must_exist" else x.closed))
            return (data.draw(principals), self.form(data, cmd, t, CHANGES[0]), []) if t else None
        if not opened:
            return None
        if cmd == "stream.close":
            return (pick(others), self.form(data, cmd, s), [])
        if reason not in ("only_opener_can_create", "change_id_must_be_new", "change_must_exist") and not s.undecided():
            unused = [c for c in CHANGES if not s.noted("change", c)]  # set up: most targets need a live change
            if unused:
                self.send(s.opener, self.form(data, "change.create", s, pick(unused)), [])
        live = s.undecided()
        new = [c for c in CHANGES if not s.noted("change", c)]
        decided = [k for k in s.changes() if s.decided(k)]
        unpulled = lambda ks: [k for k in ks if not s.noted("pulled", k)]
        if reason == "only_opener_can_create":
            return (pick(others), self.form(data, cmd, s, pick(new) or k0), [])
        if reason == "change_id_must_be_new":
            k = pick(s.changes())
            return (s.opener, self.form(data, cmd, s, k), []) if k else None
        if reason == "change_must_exist":
            k = pick(new)
            actor = pick(others) if cmd in ("change.push", "change.review") else s.opener
            return (actor, self.form(data, cmd, s, k), []) if k else None
        if reason == "revisions_must_be_unique":
            k = pick(k for k in live if s.revisions(k))
            if k is None:
                return None
            url = pick(s.revisions(k))
            actor = {"change.branch": s.opener, "change.merge": s.opener,
                     "change.push": pick(s.developers(k)),
                     "change.review": pick(p for p in others if p not in s.developers(k))}[cmd]
            return (actor, self.form(data, cmd, s, k, url=url), []) if actor else None
        if reason == "only_opener_can_branch":
            k = pick(live)
            return (pick(others), self.form(data, cmd, s, k), []) if k else None
        if reason == "developer_must_not_be_the_opener":
            k = pick(live)
            return (s.opener, self.form(data, cmd, s, k, developer=s.opener), []) if k else None
        if reason == "developer_is_branched_once":
            k = pick(k for k in unpulled(live) if s.developers(k))
            return (s.opener, self.form(data, cmd, s, k, developer=pick(s.developers(k))), []) if k else None
        if reason == "developer_must_not_be_a_reviewer":
            k = pick(k for k in unpulled(live) if set(s.reviewers(k)) - set(s.developers(k)))
            if k is None:
                return None
            return (s.opener, self.form(data, cmd, s, k, developer=pick(set(s.reviewers(k)) - set(s.developers(k)))), [])
        if reason == "change_must_not_be_pulled":
            k = pick(k for k in live if s.noted("pulled", k) and (cmd == "change.branch" and self.fresh_developer(s, k)
                                                                   or cmd == "change.push" and s.developers(k)))
            if k is None:
                return None
            actor = s.opener if cmd == "change.branch" else pick(s.developers(k))
            return (actor, self.form(data, cmd, s, k), [])
        if reason == "only_branched_developers_can_push":
            k = pick(unpulled(live))
            return (pick(p for p in PRINCIPALS if p not in s.developers(k)), self.form(data, cmd, s, k), []) if k else None
        if reason == "only_opener_can_pull":
            k = pick(live)
            return (pick(others), self.form(data, cmd, s, k), []) if k else None
        if reason == "change_is_pulled_once":
            k = pick(k for k in live if s.noted("pulled", k))
            return (s.opener, self.form(data, cmd, s, k), []) if k else None
        if reason == "reviewer_must_not_be_a_developer":
            k = pick(k for k in live if s.developers(k))
            return (pick(s.developers(k)), self.form(data, cmd, s, k), []) if k else None
        if reason == "reviewer_must_not_be_the_opener":
            k = pick(live)
            return (s.opener, self.form(data, cmd, s, k), []) if k else None
        if reason == "only_opener_can_decide":
            k = pick(live)
            return (pick(others), self.form(data, cmd, s, k), []) if k else None
        if reason == "change_is_decided_once":
            k = pick(decided)
            return (s.opener, self.form(data, cmd, s, k), []) if k else None
        if reason == "change_must_be_undecided":
            if cmd == "change.review":
                k = pick(decided)
                actor = pick(p for p in others if p not in s.developers(k)) if k else None
            elif cmd == "change.pull":
                k = pick(unpulled(decided))
                actor = s.opener
            elif cmd == "change.branch":
                k = pick(k for k in unpulled(decided) if self.fresh_developer(s, k))
                actor = s.opener
            else:
                k = pick(k for k in unpulled(decided) if s.developers(k))
                actor = pick(s.developers(k)) if k else None
            return (actor, self.form(data, cmd, s, k), []) if k and actor else None
        raise AssertionError((cmd, reason))

    def aimed(self, data):
        """One aimed refusal: the target drawn, then the next targets in turn until one can be built from this state.
        The step count is mixed into the draw so that targets rotate even where Hypothesis favours small draws."""
        start = data.draw(st.integers(0, len(TARGETS) - 1)) + self.steps
        for offset in range(len(TARGETS)):
            cmd, reason = TARGETS[(start + offset) % len(TARGETS)]
            built = self.aim(data, cmd, reason)
            if built is not None:
                actor, f, fresh = built
                self.send(actor, f, fresh)
                return

    # ---- two rules at once: a request that two rules of the same command both refuse, so that the first in the
    # engine's order is the one that must answer (the order mutants of mutants.py die of these) ----

    def violate(self, data, s, cmd, reasons):
        """`(actor, command, [])` that breaks every rule in `reasons` (all of `cmd`), built from stream `s`: a change
        meeting each rule's condition, the valid actor and fields, then each rule's violation applied. None when the
        state has no such change or the violations conflict."""
        def pick(xs):
            xs = list(xs)
            return data.draw(st.sampled_from(xs)) if xs else None
        if s.opener is None or s.closed:
            return None
        others = [p for p in PRINCIPALS if p != s.opener]
        conds = {"change_id_must_be_new": lambda k: s.noted("change", k),
                 "change_must_exist": lambda k: not s.noted("change", k),
                 "revisions_must_be_unique": lambda k: s.revisions(k),
                 "developer_is_branched_once": lambda k: s.developers(k),
                 "developer_must_not_be_a_reviewer": lambda k: set(s.reviewers(k)) - set(s.developers(k)),
                 "change_must_not_be_pulled": lambda k: s.noted("pulled", k),
                 "change_is_pulled_once": lambda k: s.noted("pulled", k),
                 "reviewer_must_not_be_a_developer": lambda k: s.developers(k),
                 "change_is_decided_once": lambda k: s.decided(k),
                 "change_must_be_undecided": lambda k: s.decided(k)}
        ks = [k for k in CHANGES if all(conds[r](k) for r in reasons if r in conds)]
        if "change_must_exist" not in reasons:
            ks = [k for k in ks if s.noted("change", k)]
        k = pick(ks)
        if k is None:
            return None
        f = self.form(data, cmd, s, k)
        actor = {"change.push": pick(s.developers(k)),
                 "change.review": pick(p for p in others if p not in s.developers(k))}.get(cmd, s.opener)
        if cmd == "change.branch":
            fresh = self.fresh_developer(s, k)
            f["developer_id"] = pick(fresh) or data.draw(principals)
        for r in reasons:
            if r in ("only_opener_can_create", "only_opener_can_branch", "only_opener_can_pull", "only_opener_can_decide",
                     "reviewer_must_not_be_the_opener"):
                actor = s.opener if r == "reviewer_must_not_be_the_opener" else pick(others)
            elif r == "only_branched_developers_can_push":
                actor = pick(p for p in PRINCIPALS if p not in s.developers(k))
            elif r == "reviewer_must_not_be_a_developer":
                actor = pick(s.developers(k))
            elif r == "revisions_must_be_unique":
                f[M.REVISION_FIELD[cmd]] = pick(s.revisions(k))
            elif r == "developer_must_not_be_the_opener":
                f["developer_id"] = s.opener
            elif r == "developer_is_branched_once":
                f["developer_id"] = pick(s.developers(k))
            elif r == "developer_must_not_be_a_reviewer":
                f["developer_id"] = pick(set(s.reviewers(k)) - set(s.developers(k)))
        if actor is None or f.get("developer_id") is None and cmd == "change.branch":
            return None
        return (actor, f, [])

    @rule(data=st.data())
    def aimed_pair(self, data):
        start = data.draw(st.integers(0, len(PAIR_TARGETS) - 1)) + self.steps
        opened = [x for x in self.streams.values() if x.opened and not x.closed and x.changes()]
        if not opened:
            return
        s = data.draw(st.sampled_from(opened))
        for offset in range(len(PAIR_TARGETS)):
            cmd, a, b = PAIR_TARGETS[(start + offset) % len(PAIR_TARGETS)]
            built = self.violate(data, s, cmd, (a, b))
            if built is not None:
                actor, f, fresh = built
                self.send(actor, f, fresh)
                return

    # three rules of the same kind: Hypothesis draws rules uniformly, and the refusals need about a third of the steps
    @rule(data=st.data())
    def aimed_refusal(self, data):
        self.aimed(data)

    @rule(data=st.data())
    def aimed_refusal_too(self, data):
        self.aimed(data)

    @rule(data=st.data())
    def aimed_refusal_again(self, data):
        self.aimed(data)

    # ---- the acceptance theorem, exercised as a rule ----

    def undecided(self):
        return [(s, k) for s in self.streams.values() if s.opened and not s.closed for k in s.undecided()]

    def unnamed(self, data, stream, k):
        free = [u for u in GOOD_URLS if not stream.revision_named(k, u)]
        if free and data is not None:
            return data.draw(st.sampled_from(free))
        self.fresh_counter += 1
        return "https://example.org/repo/commit/fresh%d" % self.fresh_counter

    @precondition(lambda self: bool(self.undecided()))
    @rule(data=st.data())
    def the_creator_can_always_merge(self, data):
        """Whatever happened before: an undecided change on an open stream, a revision not yet named on it, the
        opener's merge is accepted."""
        if data.draw(st.sampled_from([True] * 3 + [False])):
            return
        stream, k = data.draw(st.sampled_from(self.undecided()))
        f = {"command": "change.merge", "stream_id": stream.id, "change_id": k,
             "merged_revision_url": self.unnamed(data, stream, k)}
        got = self.send(stream.opener, f)
        self.check(got.get("accept") is True, "the_creator_can_always_merge", got)
        EXTRA["the_creator_can_always_merge: as a rule"] += 1

    # ---- the acceptance theorem, at every step ----

    @invariant()
    def the_creator_can_always_merge_everywhere(self):
        """After every step: for each undecided change on an open stream, the opener's merge at an unnamed revision is
        accepted by the engine from this very state; the state is then restored from its snapshot."""
        for s in self.streams.values():
            if not (s.opened and not s.closed):
                continue
            live = s.undecided()
            if not live:
                continue
            snap = self.engine.snapshot(s.id)
            self.check(snap["k"] == len(s.events), "the snapshot's length", snap["k"], len(s.events))
            for k in live:
                u = self.unnamed(None, s, k)
                req = {"actor_id": s.opener, "fresh": [],
                       "command": {"command": "change.merge", "stream_id": s.id, "change_id": k, "merged_revision_url": u}}
                self.check(M.judge(s, req) is None, "the model must accept the opener's merge", req)
                got = self.engine.decide(req)
                RUNS["requests"] += 1
                self.trace.append({"request": req, "answer": got, "want": None, "probe": True})
                self.check(got.get("accept") is True and got["at"] == len(s.events), "the_creator_can_always_merge",
                           req, got)
                self.check(got["event"] == M.event_of(req, s.id), "the probe merge's event", got["event"])
                self.engine.load(s.id, snap["k"], snap["state"])
                EXTRA["the_creator_can_always_merge: as a probe"] += 1
            got = self.engine.query({"query": "stream", "stream_id": s.id})
            self.check(got == s.read(), "the read after the snapshot is loaded back", got, s.read())

    # ---- the theorems, as invariants of the accepted log ----

    @invariant()
    def theorems_hold(self):
        for s in self.streams.values():
            if not s.opened:
                self.check(not s.events, "events on a stream never opened")
                continue
            opener = s.opener
            created, developers, reviewers, pulled, decided = set(), {}, {}, set(), set()
            revisions = {}
            for e in s.events:
                name = e["event"]
                if name in ("stream.opened", "stream.closed"):
                    if name == "stream.closed":
                        self.check(e["actor_id"] == opener, "only_the_opener_closes_the_stream")
                        self.check(e is s.events[-1], "nothing_follows_a_close")
                    continue
                k = e["change_id"]
                if name != "change.created":
                    self.check(k in created, "every_event_names_a_created_change")
                self.check(k not in decided, "nothing_follows_a_decision")
                rev = {"change.created": "from_revision_url", "change.branched": "branch_revision_url",
                       "change.pushed": "pushed_revision_url", "change.reviewed": "reviewed_revision_url",
                       "change.merged": "merged_revision_url"}.get(name)
                if rev:
                    self.check(e[rev] not in revisions.setdefault(k, set()), "revisions_are_distinct")
                    revisions[k].add(e[rev])
                if name == "change.created":
                    self.check(e["actor_id"] == opener, "every_change_is_created_by_the_opener")
                    self.check(k not in created, "a_change_is_created_once")
                    created.add(k)
                elif name == "change.branched":
                    d = e["developer_id"]
                    self.check(e["actor_id"] == opener, "every_branch_is_by_the_opener")
                    self.check(d != opener, "no_developer_is_the_opener")
                    self.check(d not in developers.setdefault(k, set()), "a_developer_is_branched_once")
                    self.check(d not in reviewers.get(k, set()), "no_developer_is_a_reviewer")
                    self.check(k not in pulled, "nothing_is_branched_or_pushed_after_the_pull")
                    developers[k].add(d)
                elif name == "change.pushed":
                    self.check(e["actor_id"] in developers.get(k, set()), "every_push_is_by_a_branched_developer")
                    self.check(k not in pulled, "nothing_is_branched_or_pushed_after_the_pull")
                elif name == "change.pulled":
                    self.check(e["actor_id"] == opener, "the_pull_is_by_the_opener")
                    self.check(k not in pulled, "a_change_is_pulled_once")
                    pulled.add(k)
                elif name == "change.reviewed":
                    r = e["actor_id"]
                    self.check(r != opener, "no_reviewer_is_the_opener")
                    self.check(r not in developers.get(k, set()), "no_developer_is_a_reviewer")
                    reviewers.setdefault(k, set()).add(r)
                elif name in ("change.merged", "change.abandoned"):
                    self.check(e["actor_id"] == opener, "the_merge_is_by_the_opener / the_abandon_is_by_the_opener")
                    self.check(k not in decided, "a_change_is_decided_once")
                    decided.add(k)
                else:
                    self.fail("an event the theorems do not know", name)
            for k in created:
                self.check(not (developers.get(k, set()) & reviewers.get(k, set())), "roles_are_disjoint")

    @invariant()
    def read_is_the_notes(self):
        for s in self.streams.values():
            got = self.engine.query({"query": "stream", "stream_id": s.id})
            self.check(got == s.read(), "the read is the notes", got, s.read())


EXAMPLES = int(os.environ.get("SOLO_EXAMPLES", "400"))
STEPS = int(os.environ.get("SOLO_STEPS", "80"))
TestSoloChangeControl = SoloChangeControl.TestCase
TestSoloChangeControl.settings = settings(max_examples=EXAMPLES, stateful_step_count=STEPS, deadline=None,
                                          database=None, derandomize=RECORDING,
                                          suppress_health_check=[HealthCheck.too_slow])


# -- what the run must have exercised ---------------------------------------------------------------------------------

def _ran():
    if RUNS["runs"] == 0:
        pytest.skip("the state machine did not run in this session")


def test_coverage_is_complete():
    """Derived from the engine's own description, not from a list here: every (command, rule) the description lists was
    the reason of some refusal; every command was accepted at least once and refused as malformed at least once; a wrong
    number of fresh ids was refused on an open and on a layer command; the acceptance theorem fired as a rule."""
    _ran()
    e = Engine([ENGINE])
    e.start()
    try:
        described = e.describe()["schema"]["commands"]
    finally:
        e.stop()
    expected = set()
    for c in described:
        for r in c["rules"]:
            expected.add((c["name"], r))
        expected.add((c["name"], "accepted"))
        expected.add((c["name"], "malformed"))
    expected.add(("stream.open", "fresh_ids_must_match_the_command"))
    expected.add(("change.create", "fresh_ids_must_match_the_command"))
    missing = sorted(p for p in expected if SEEN[p] == 0)
    assert not missing, "never observed in %d runs: %s" % (RUNS["runs"], missing)
    unexpected = sorted(p for p in SEEN if p not in expected and p[1] != "accepted")
    assert not unexpected, "observed but not described: %s" % unexpected
    assert EXTRA["the_creator_can_always_merge: as a rule"] > 0, "the acceptance theorem never fired as a rule"
    assert EXTRA["the_creator_can_always_merge: as a probe"] > 0, "the acceptance theorem was never probed"


def test_description_is_the_model():
    """The engine describes the commands, fields, kinds and rule order the model restates."""
    e = Engine([ENGINE])
    e.start()
    try:
        described = e.describe()["schema"]["commands"]
    finally:
        e.stop()
    assert [c["name"] for c in described] == list(M.COMMANDS)
    for c in described:
        assert [(p["name"], p["kind"]) for p in c["params"]] == M.SCHEMA[c["name"]], c["name"]
        assert c["rules"] == M.expected_rules(c["name"]), c["name"]
        assert c["event"]["name"] == M.EVENT_OF[c["name"]]
        assert c["fresh"] == M.FRESH.get(c["name"], 0)
    assert set(M.RULE_NAMES) == {r for c in described for r in c["rules"]} - set(M.ADMISSION) - \
        {"stream_id_must_be_new", "revision_url_must_name_a_commit", "only_opener_can_close"}


def test_deep_states_are_reached():
    _ran()
    missing = [name for name in DEEP_STATES if DEEP[name] == 0]
    assert not missing, "deep states never reached in %d runs: %s" % (RUNS["runs"], missing)


def test_record_cases():
    """With SOLO_RECORD set: the best passing sequences of this run, as conformance cases (cases/solochangecontrol.jsonl)."""
    if not RECORDING:
        pytest.skip("set SOLO_RECORD=1 to write cases")
    _ran()
    chosen = []
    for score, name, trace in sorted(PASSING, key=lambda x: -x[0]):
        try:
            record.cases_of(trace, name)
        except record.Unrepresentable:
            continue
        chosen.append((name, trace))
        if len(chosen) == 6:
            break
    assert chosen, "no passing sequence a host could run"
    n = record.write_theme(chosen, CASES_PATH)
    print("\nwrote %d cases from %d sequences to %s" % (n, len(chosen), CASES_PATH), file=sys.stderr)
