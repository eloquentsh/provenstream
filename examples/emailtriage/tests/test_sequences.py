# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Random command sequences against the compiled emailtriage engine (Hypothesis, stateful), with requirements on what
the run must have exercised. The shape is examples/email/tests/test_sequences.py's (its docstring explains it); here
the vocabulary is the triage's, the cutoff is the first review, and the acceptance theorem is
`the_creator_can_always_ignore`.

    PYTHONPATH=host python3 -m pytest examples/emailtriage/tests -q

TRIAGE_EXAMPLES and TRIAGE_STEPS set the budget (default 400 x 80). TRIAGE_ENGINE names another engine.
"""
from __future__ import annotations
import atexit, collections, json, os, sys, uuid

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(REPO, "host"))
sys.path.insert(0, HERE)

import pytest
from hypothesis import HealthCheck, settings, strategies as st
from hypothesis.stateful import RuleBasedStateMachine, initialize, invariant, precondition, rule

from provenstream.engine import Engine
import triage_model as M

ENGINE = os.environ.get("TRIAGE_ENGINE") or os.path.join(REPO, "examples", "emailtriage", ".lake", "build", "bin", "emailtriage-engine")
DUMP_DIR = os.environ.get("TRIAGE_DUMP") or os.path.join(HERE, ".hypothesis")
NS = uuid.UUID("12345678-1234-5678-1234-567812345678")


def U(name: str) -> str:
    return str(uuid.uuid5(NS, name))


ANN, BEN, CY, DEE, EVE, FAY = (U(p) for p in ("ann", "ben", "cy", "dee", "eve", "fay"))
PRINCIPALS = [ANN, BEN, CY, DEE, EVE, FAY]
S, T = U("stream-s"), U("stream-t")
STREAMS = [S, T]
TRIAGES = [U("triage-%d" % i) for i in range(4)]
EMAILS = [U("email-%d" % i) for i in range(4)]
PROOF_URL = M.PROOF_URL
GOOD_EMLS = ["eloquentmail://personal/m%d.eml" % i for i in range(6)]
BAD_EMLS = ["", "no-scheme.eml", "https://", "://host.eml", "https://a b/c.eml", "a://b://c.eml", "eloquentmail://personal/m1", "eloquentmail://personal/m1.EML"]
BAD_VERDICTS = ["", "Reply", "delegate", "reply ", "maybe", 1, None]
BAD_PROOF_URLS = ["https://example.org/provenstream/commit/0123456789abcdef", PROOF_URL.upper(),
                  "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567",
                  "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/../x",
                  "https://example.org/commit/0123456789abcdef0123456789abcdef01234567", "ftp:/x/commit/" + "0" * 40]

SEEN = collections.Counter()
EXTRA = collections.Counter()
DEEP = collections.Counter()
RUNS = collections.Counter()

TARGETS = [(cmd, r) for cmd in M.COMMANDS for r in M.expected_rules(cmd)] + \
          [(cmd, "malformed") for cmd in M.COMMANDS] + \
          [("stream.open", "fresh_ids_must_match_the_command"), ("triage.create", "fresh_ids_must_match_the_command")]
PAIR_TARGETS = [(cmd, a, b) for cmd in M.LAYER for i, a in enumerate(M.rules_of(cmd)) for b in M.rules_of(cmd)[i + 1:]]

DEEP_STATES = ("a reply after a review", "an ignore after a review that said reply", "two distinct reviewers on one triage",
               "advice by two advisers on one triage", "advice that disagrees", "a review with no advice",
               "an ignore with no ask", "a close while a triage is undecided", "both streams open at once")


@atexit.register
def _report():
    if not SEEN:
        return
    print("\nemailtriage sequences: %d runs, %d steps, %d requests" % (RUNS["runs"], RUNS["steps"], RUNS["requests"]), file=sys.stderr)
    width = max(len("%s %s" % k) for k in SEEN)
    for (cmd, outcome), n in sorted(SEEN.items(), key=lambda kv: (kv[0][0], -kv[1], kv[0][1])):
        print("  %-*s %7d" % (width, "%s %s" % (cmd, outcome), n), file=sys.stderr)
    for k, n in sorted(EXTRA.items()):
        print("  %-*s %7d" % (width, k, n), file=sys.stderr)
    print("deep states reached (runs):", file=sys.stderr)
    for name in DEEP_STATES:
        print("  %-*s %7d" % (width, name, DEEP[name]), file=sys.stderr)


principals = st.sampled_from(PRINCIPALS)
triages = st.sampled_from(TRIAGES)
verdicts = st.sampled_from(["reply", "ignore"])
metas = st.one_of(st.none(), st.text(alphabet=st.characters(min_codepoint=32, max_codepoint=0x7e), max_size=12))


def dump_failing(trace, failure, where):
    os.makedirs(where, exist_ok=True)
    with open(os.path.join(where, "failing.trace.json"), "w", encoding="utf-8") as f:
        json.dump({"failure": [repr(x) for x in failure], "trace": trace}, f, indent=1, default=str)


def deep_states(streams) -> set:
    reached = set()
    both = False
    for s in streams.values():
        if not s.opened:
            continue
        by = collections.defaultdict(list)
        for e in s.events:
            if "triage_id" in e:
                by[e["triage_id"]].append(e)
        for k, evs in by.items():
            names = [e["event"] for e in evs]
            calls = [e["verdict"] for e in evs if e["event"] == "triage.reviewed"]
            advice = [e["verdict"] for e in evs if e["event"] == "triage.advised"]
            if "triage.reviewed" in names and "triage.replied" in names:
                reached.add("a reply after a review")
            if calls and "reply" in calls and "triage.ignored" in names:
                reached.add("an ignore after a review that said reply")
            if len({e["actor_id"] for e in evs if e["event"] == "triage.reviewed"}) >= 2:
                reached.add("two distinct reviewers on one triage")
            if len({e["actor_id"] for e in evs if e["event"] == "triage.advised"}) >= 2:
                reached.add("advice by two advisers on one triage")
            if len(set(advice)) == 2:
                reached.add("advice that disagrees")
            if "triage.reviewed" in names and "triage.advised" not in names:
                reached.add("a review with no advice")
            if "triage.ignored" in names and "triage.asked" not in names:
                reached.add("an ignore with no ask")
        if s.closed and s.undecided():
            reached.add("a close while a triage is undecided")
        both = both or getattr(s, "opened_while_other_open", False)
    if both:
        reached.add("both streams open at once")
    return reached


class TriageMachine(RuleBasedStateMachine):
    def __init__(self):
        super().__init__()
        self.engine = Engine([ENGINE])
        self.engine.start()
        self.model = M.Model()
        for sid in STREAMS:
            self.model.stream(sid)
        self.steps = 0
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
            dump_failing(self.trace, self.failure, DUMP_DIR)
            return
        for name in deep_states(self.streams):
            DEEP[name] += 1

    def fail(self, *why):
        self.failure = why
        raise AssertionError(why)

    def check(self, cond, *why):
        if not cond:
            self.fail(*why)

    def send(self, actor, cmd, fresh=None):
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

    # ---- choosing ----

    def pick_stream(self, data):
        return data.draw(st.sampled_from([S] * 4 + [T]))

    def pick_actor(self, data, stream, prefer):
        if stream.opener is not None and prefer is not None and data.draw(st.sampled_from([True] * 4 + [False])):
            if prefer == "opener":
                return stream.opener
            k = prefer[1]
            advisers = stream.advisers(k)
            if prefer[0] == "adviser" and advisers:
                return data.draw(st.sampled_from(advisers))
            if prefer[0] == "reviewer":
                return self.pick_reviewer(data, stream, k)
        return data.draw(principals)

    def pick_triage(self, data, stream, prefer_undecided=True, ripe=None):
        created = stream.triages()
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
        return data.draw(triages)

    def pick_eml(self, data):
        return data.draw(st.sampled_from(GOOD_EMLS * 3 + BAD_EMLS[:3]))

    def pick_verdict(self, data):
        roll = data.draw(st.integers(0, 11))
        return data.draw(st.sampled_from(BAD_VERDICTS)) if roll == 0 else data.draw(verdicts)

    def with_meta(self, data, f):
        m = data.draw(metas)
        if m is not None:
            f["meta"] = m
        if data.draw(st.integers(0, 59)) == 0:
            f["meta"] = data.draw(st.sampled_from(["a\tb", "x\x00y", "\x7f", "é" * 2048 + "a"]))
        return f

    def mangle(self, data, f, always=False):
        if not always and data.draw(st.integers(0, 39)) != 0:
            return f
        how = data.draw(st.sampled_from(["upper", "extra", "missing"]))
        uuids = [k for k, v in f.items() if k != "command" and M.valid_uuid(v) and any(c.isalpha() for c in v)]
        required = [k for k in f if k not in ("command", "meta")]
        if how == "upper" and uuids:
            k = data.draw(st.sampled_from(uuids))
            f[k] = f[k].upper()
        elif how == "missing" and required:
            del f[data.draw(st.sampled_from(required))]
        else:
            f["extra"] = 1
        return f

    def life(self, stream, k):
        return sum(1 for e in stream.events if e.get("triage_id") == k)

    def fresh_adviser(self, stream, k):
        return [p for p in PRINCIPALS if p != stream.opener and p not in stream.advisers(k) and p not in stream.reviewers(k)]

    def pick_adviser(self, data, stream, k):
        if stream.opener is None:
            return data.draw(principals)
        roll = data.draw(st.integers(0, 7))
        if roll == 0:
            return stream.opener
        if roll == 1 and stream.advisers(k):
            return data.draw(st.sampled_from(stream.advisers(k)))
        if roll == 2 and stream.reviewers(k):
            return data.draw(st.sampled_from(stream.reviewers(k)))
        fresh = self.fresh_adviser(stream, k)
        return data.draw(st.sampled_from(fresh)) if fresh else data.draw(principals)

    def pick_reviewer(self, data, stream, k):
        able = [p for p in PRINCIPALS if p != stream.opener and p not in stream.advisers(k)]
        again = [p for p in able if p in stream.reviewers(k)]
        pool = again if again and data.draw(st.sampled_from([True] * 2 + [False])) else able
        return data.draw(st.sampled_from(pool)) if pool else data.draw(principals)

    # ---- the core ----

    @initialize(data=st.data())
    def maybe_open(self, data):
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
        k = data.draw(triages)
        f = {"command": "triage.create", "stream_id": sid, "triage_id": k, "message_url": self.pick_eml(data)}
        fresh = [U("extra")] if data.draw(st.integers(0, 19)) == 0 else []
        self.send(actor, self.mangle(data, self.with_meta(data, f)), fresh)

    @rule(data=st.data())
    def ask(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        actor = self.pick_actor(data, stream, "opener")
        k = self.pick_triage(data, stream, ripe=lambda k: len(stream.advisers(k)) == 1 and not stream.reviewed(k))
        d = self.pick_adviser(data, stream, k)
        f = {"command": "triage.ask", "stream_id": sid, "triage_id": k, "adviser_id": d}
        self.send(actor, self.mangle(data, self.with_meta(data, f)))

    @rule(data=st.data())
    def advise(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        decided = [k for k in stream.triages() if stream.decided(k) and not stream.reviewed(k)]
        if decided and data.draw(st.integers(0, 7)) == 0:
            k = data.draw(st.sampled_from(decided))
        else:
            k = self.pick_triage(data, stream)
        actor = self.pick_actor(data, stream, ("adviser", k))
        f = {"command": "triage.advise", "stream_id": sid, "triage_id": k, "verdict": self.pick_verdict(data)}
        self.send(actor, self.mangle(data, self.with_meta(data, f)))

    @rule(data=st.data())
    def review(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        k = self.pick_triage(data, stream)
        actor = self.pick_actor(data, stream, ("reviewer", k))
        advisers = stream.advisers(k)
        if advisers and data.draw(st.sampled_from([False] * 7 + [True])):
            actor = data.draw(st.sampled_from(advisers))
        if self.life(stream, k) < 2 and data.draw(st.sampled_from([True] * 2 + [False])):
            return
        f = {"command": "triage.review", "stream_id": sid, "triage_id": k, "verdict": self.pick_verdict(data)}
        self.send(actor, self.mangle(data, self.with_meta(data, f)))

    @rule(data=st.data())
    def reply(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        actor = self.pick_actor(data, stream, "opener")
        k = self.pick_triage(data, stream, prefer_undecided=False)
        hold = 5 if self.life(stream, k) < 6 else 1
        if data.draw(st.sampled_from([True] * hold + [False])):
            return
        f = {"command": "triage.reply", "stream_id": sid, "triage_id": k, "email_id": data.draw(st.sampled_from(EMAILS))}
        self.send(actor, self.mangle(data, self.with_meta(data, f)))

    @rule(data=st.data())
    def ignore(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        actor = self.pick_actor(data, stream, "opener")
        k = self.pick_triage(data, stream, prefer_undecided=False)
        hold = 5 if self.life(stream, k) < 6 else 1
        if data.draw(st.sampled_from([True] * hold + [False])):
            return
        self.send(actor, self.mangle(data, self.with_meta(data, {"command": "triage.ignore", "stream_id": sid, "triage_id": k})))

    # ---- scenarios ----

    def live_triage(self, data, stream, ripe):
        good = [k for k in stream.undecided() if ripe(k)] if stream.opened and not stream.closed else []
        return data.draw(st.sampled_from(good)) if good else None

    def layer(self, data, actor, cmd, stream, k, **fields):
        f = {"command": cmd, "stream_id": stream.id, "triage_id": k}
        f.update(fields)
        return self.send(actor, self.with_meta(data, f))

    @rule(data=st.data())
    def scenario_two_advisers_disagree(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        k = self.live_triage(data, stream, lambda k: not stream.reviewed(k) and len(stream.advisers(k)) <= 2)
        if k is None:
            return
        advisers = stream.advisers(k)
        while len(advisers) < 2:
            fresh = self.fresh_adviser(stream, k)
            if not fresh:
                return
            self.layer(data, stream.opener, "triage.ask", stream, k, adviser_id=data.draw(st.sampled_from(fresh)))
            advisers = stream.advisers(k)
        for d, v in zip(advisers[-2:], ("reply", "ignore")):
            if d not in stream.advised(k):
                self.layer(data, d, "triage.advise", stream, k, verdict=v)

    @rule(data=st.data())
    def scenario_two_reviewers(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        k = self.live_triage(data, stream, lambda k: len(set(stream.reviewers(k))) <= 1)
        if k is None:
            return
        able = [p for p in PRINCIPALS if p != stream.opener and p not in stream.advisers(k) and p not in stream.reviewers(k)]
        for r in able[:2]:
            self.layer(data, r, "triage.review", stream, k, verdict=data.draw(verdicts))

    @rule(data=st.data())
    def scenario_review_then_decide(self, data):
        """Advice, a review, and the opener's decision: a reply when the call was reply (most of the time), an ignore
        otherwise, sometimes against the call."""
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        k = self.live_triage(data, stream, lambda k: self.life(stream, k) >= 1)
        if k is None:
            return
        if not stream.reviewers(k):
            self.layer(data, self.pick_reviewer(data, stream, k), "triage.review", stream, k, verdict=data.draw(verdicts))
        calls = [e["verdict"] for e in stream.events if e.get("triage_id") == k and e["event"] == "triage.reviewed"]
        follow = data.draw(st.sampled_from([True] * 3 + [False]))
        want = calls[-1] if calls and follow else ("ignore" if calls and calls[-1] == "reply" else "reply")
        if want == "reply":
            self.layer(data, stream.opener, "triage.reply", stream, k, email_id=data.draw(st.sampled_from(EMAILS)))
        else:
            self.layer(data, stream.opener, "triage.ignore", stream, k)

    @rule(data=st.data())
    def scenario_decided_before_any_review(self, data):
        """A triage with an asked adviser is decided before any review; the adviser's advice and a further ask then meet
        triage_must_be_undecided, which needs exactly this state (a review would answer first with
        triage_must_not_be_reviewed)."""
        if data.draw(st.sampled_from([True] * 3 + [False])):
            return
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        k = self.live_triage(data, stream, lambda k: not stream.reviewed(k))
        if k is None:
            return
        waiting = [d for d in stream.advisers(k) if d not in stream.advised(k)]
        if not waiting:
            fresh = self.fresh_adviser(stream, k)
            if not fresh:
                return
            d = data.draw(st.sampled_from(fresh))
            self.layer(data, stream.opener, "triage.ask", stream, k, adviser_id=d)
            waiting = [d]
        if data.draw(st.booleans()):
            self.layer(data, stream.opener, "triage.reply", stream, k, email_id=data.draw(st.sampled_from(EMAILS)))
        else:
            self.layer(data, stream.opener, "triage.ignore", stream, k)
        self.layer(data, data.draw(st.sampled_from(waiting)), "triage.advise", stream, k, verdict=data.draw(verdicts))
        fresh = self.fresh_adviser(stream, k)
        if fresh:
            self.layer(data, stream.opener, "triage.ask", stream, k, adviser_id=data.draw(st.sampled_from(fresh)))

    # ---- refusals, aimed ----

    def form(self, data, cmd, stream, k=None, adviser=None):
        f = {"command": cmd}
        if cmd == "stream.open":
            f["proof_revision_url"] = PROOF_URL
            return f
        f["stream_id"] = stream.id
        if cmd == "stream.close":
            return f
        f["triage_id"] = k
        if cmd == "triage.create":
            f["message_url"] = data.draw(st.sampled_from(GOOD_EMLS))
        if cmd == "triage.ask":
            fresh = self.fresh_adviser(stream, k)
            f["adviser_id"] = adviser or (data.draw(st.sampled_from(fresh)) if fresh else data.draw(principals))
        if cmd in ("triage.advise", "triage.review"):
            f["verdict"] = data.draw(verdicts)
        if cmd == "triage.reply":
            f["email_id"] = data.draw(st.sampled_from(EMAILS))
        return f

    def aim(self, data, cmd, reason):
        def pick(xs):
            xs = list(xs)
            return data.draw(st.sampled_from(xs)) if xs else None

        streams = list(self.streams.values())
        opened = [s for s in streams if s.opened and not s.closed]
        s = pick([x for x in opened if x.undecided()] or opened) or self.streams[S]
        k0 = pick(s.triages()) or TRIAGES[0]
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
            if t is None:
                return None
            f = self.form(data, cmd, t); f["proof_revision_url"] = pick(BAD_PROOF_URLS)
            return (data.draw(principals), f, [t.id])
        if reason == "stream_must_be_open" and not any(x.closed for x in streams):
            spare = [x for x in opened if x is not s]
            if spare:
                self.send(spare[0].opener, self.form(data, "stream.close", spare[0]), [])
        if reason in ("stream_must_exist", "stream_must_be_open"):
            t = pick(x for x in streams if (not x.opened if reason == "stream_must_exist" else x.closed))
            return (data.draw(principals), self.form(data, cmd, t, TRIAGES[0]), []) if t else None
        if not opened:
            return None
        if cmd == "stream.close":
            return (pick(others), self.form(data, cmd, s), [])
        if reason not in ("only_opener_can_create", "triage_id_must_be_new", "triage_must_exist") and not s.undecided():
            unused = [c for c in TRIAGES if not s.noted("triage", c)]
            if unused:
                self.send(s.opener, self.form(data, "triage.create", s, pick(unused)), [])
        live = s.undecided()
        new = [c for c in TRIAGES if not s.noted("triage", c)]
        decided = [k for k in s.triages() if s.decided(k)]
        unreviewed = lambda ks: [k for k in ks if not s.reviewed(k)]
        if reason == "only_opener_can_create":
            return (pick(others), self.form(data, cmd, s, pick(new) or k0), [])
        if reason == "triage_id_must_be_new":
            k = pick(s.triages())
            return (s.opener, self.form(data, cmd, s, k), []) if k else None
        if reason == "triage_must_exist":
            k = pick(new)
            actor = pick(others) if cmd in ("triage.advise", "triage.review") else s.opener
            return (actor, self.form(data, cmd, s, k), []) if k else None
        if reason == "only_opener_can_ask":
            k = pick(live)
            return (pick(others), self.form(data, cmd, s, k), []) if k else None
        if reason == "adviser_must_not_be_the_opener":
            k = pick(live)
            return (s.opener, self.form(data, cmd, s, k, adviser=s.opener), []) if k else None
        if reason == "adviser_is_asked_once":
            k = pick(k for k in unreviewed(live) if s.advisers(k))
            return (s.opener, self.form(data, cmd, s, k, adviser=pick(s.advisers(k))), []) if k else None
        if reason == "adviser_must_not_be_a_reviewer":
            k = pick(k for k in live if set(s.reviewers(k)) - set(s.advisers(k)))
            if k is None:
                return None
            return (s.opener, self.form(data, cmd, s, k, adviser=pick(set(s.reviewers(k)) - set(s.advisers(k)))), [])
        if reason == "triage_must_not_be_reviewed":
            k = pick(k for k in live if s.reviewed(k) and (cmd == "triage.ask" and self.fresh_adviser(s, k)
                                                           or cmd == "triage.advise" and [d for d in s.advisers(k) if d not in s.advised(k)]))
            if k is None:
                return None
            actor = s.opener if cmd == "triage.ask" else pick(d for d in s.advisers(k) if d not in s.advised(k))
            return (actor, self.form(data, cmd, s, k), [])
        if reason == "only_asked_advisers_can_advise":
            k = pick(unreviewed(live))
            return (pick(p for p in PRINCIPALS if p not in s.advisers(k)), self.form(data, cmd, s, k), []) if k else None
        if reason == "adviser_advises_once":
            k = pick(k for k in unreviewed(live) if s.advised(k))
            return (pick(s.advised(k)), self.form(data, cmd, s, k), []) if k else None
        if reason == "reviewer_must_not_be_an_adviser":
            k = pick(k for k in live if s.advisers(k))
            return (pick(s.advisers(k)), self.form(data, cmd, s, k), []) if k else None
        if reason == "reviewer_must_not_be_the_opener":
            k = pick(live)
            return (s.opener, self.form(data, cmd, s, k), []) if k else None
        if reason == "only_opener_can_decide":
            k = pick(live)
            return (pick(others), self.form(data, cmd, s, k), []) if k else None
        if reason == "triage_is_decided_once":
            k = pick(decided)
            return (s.opener, self.form(data, cmd, s, k), []) if k else None
        if reason == "triage_must_be_undecided":
            if cmd == "triage.review":
                k = pick(decided)
                actor = pick(p for p in others if p not in s.advisers(k)) if k else None
            elif cmd == "triage.ask":
                k = pick(k for k in unreviewed(decided) if self.fresh_adviser(s, k))
                actor = s.opener
            else:
                k = pick(k for k in unreviewed(decided) if [d for d in s.advisers(k) if d not in s.advised(k)])
                actor = pick(d for d in s.advisers(k) if d not in s.advised(k)) if k else None
            return (actor, self.form(data, cmd, s, k), []) if k and actor else None
        raise AssertionError((cmd, reason))

    def aimed(self, data):
        start = data.draw(st.integers(0, len(TARGETS) - 1)) + self.steps
        for offset in range(len(TARGETS)):
            cmd, reason = TARGETS[(start + offset) % len(TARGETS)]
            built = self.aim(data, cmd, reason)
            if built is not None:
                actor, f, fresh = built
                self.send(actor, f, fresh)
                return

    def violate(self, data, s, cmd, reasons):
        def pick(xs):
            xs = list(xs)
            return data.draw(st.sampled_from(xs)) if xs else None
        if s.opener is None or s.closed:
            return None
        others = [p for p in PRINCIPALS if p != s.opener]
        conds = {"triage_id_must_be_new": lambda k: s.noted("triage", k),
                 "triage_must_exist": lambda k: not s.noted("triage", k),
                 "adviser_is_asked_once": lambda k: s.advisers(k),
                 "adviser_must_not_be_a_reviewer": lambda k: set(s.reviewers(k)) - set(s.advisers(k)),
                 "triage_must_not_be_reviewed": lambda k: s.reviewed(k),
                 "adviser_advises_once": lambda k: s.advised(k),
                 "reviewer_must_not_be_an_adviser": lambda k: s.advisers(k),
                 "triage_is_decided_once": lambda k: s.decided(k),
                 "triage_must_be_undecided": lambda k: s.decided(k)}
        ks = [k for k in TRIAGES if all(conds[r](k) for r in reasons if r in conds)]
        if "triage_must_exist" not in reasons:
            ks = [k for k in ks if s.noted("triage", k)]
        k = pick(ks)
        if k is None:
            return None
        f = self.form(data, cmd, s, k)
        unadvised = [d for d in s.advisers(k) if d not in s.advised(k)]
        actor = {"triage.advise": pick(unadvised) or pick(s.advisers(k)),
                 "triage.review": pick(p for p in others if p not in s.advisers(k))}.get(cmd, s.opener)
        if cmd == "triage.ask":
            fresh = self.fresh_adviser(s, k)
            f["adviser_id"] = pick(fresh) or data.draw(principals)
        for r in reasons:
            if r in ("only_opener_can_create", "only_opener_can_ask", "only_opener_can_decide", "reviewer_must_not_be_the_opener"):
                actor = s.opener if r == "reviewer_must_not_be_the_opener" else pick(others)
            elif r == "only_asked_advisers_can_advise":
                actor = pick(p for p in PRINCIPALS if p not in s.advisers(k))
            elif r == "adviser_advises_once":
                actor = pick(s.advised(k))
            elif r == "reviewer_must_not_be_an_adviser":
                actor = pick(s.advisers(k))
            elif r == "adviser_must_not_be_the_opener":
                f["adviser_id"] = s.opener
            elif r == "adviser_is_asked_once":
                f["adviser_id"] = pick(s.advisers(k))
            elif r == "adviser_must_not_be_a_reviewer":
                f["adviser_id"] = pick(set(s.reviewers(k)) - set(s.advisers(k)))
        if actor is None or f.get("adviser_id") is None and cmd == "triage.ask":
            return None
        return (actor, f, [])

    @rule(data=st.data())
    def aimed_pair(self, data):
        start = data.draw(st.integers(0, len(PAIR_TARGETS) - 1)) + self.steps
        opened = [x for x in self.streams.values() if x.opened and not x.closed and x.triages()]
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

    @rule(data=st.data())
    def aimed_refusal(self, data):
        self.aimed(data)

    @rule(data=st.data())
    def aimed_refusal_too(self, data):
        self.aimed(data)

    @rule(data=st.data())
    def aimed_refusal_again(self, data):
        self.aimed(data)

    # ---- the acceptance theorem ----

    def undecided(self):
        return [(s, k) for s in self.streams.values() if s.opened and not s.closed for k in s.undecided()]

    @precondition(lambda self: bool(self.undecided()))
    @rule(data=st.data())
    def the_creator_can_always_ignore(self, data):
        if data.draw(st.sampled_from([True] * 3 + [False])):
            return
        stream, k = data.draw(st.sampled_from(self.undecided()))
        got = self.send(stream.opener, {"command": "triage.ignore", "stream_id": stream.id, "triage_id": k})
        self.check(got.get("accept") is True, "the_creator_can_always_ignore", got)
        EXTRA["the_creator_can_always_ignore: as a rule"] += 1

    @invariant()
    def the_creator_can_always_ignore_everywhere(self):
        for s in self.streams.values():
            if not (s.opened and not s.closed):
                continue
            live = s.undecided()
            if not live:
                continue
            snap = self.engine.snapshot(s.id)
            self.check(snap["k"] == len(s.events), "the snapshot's length", snap["k"], len(s.events))
            for k in live:
                req = {"actor_id": s.opener, "fresh": [], "command": {"command": "triage.ignore", "stream_id": s.id, "triage_id": k}}
                self.check(M.judge(s, req) is None, "the model must accept the opener's ignore", req)
                got = self.engine.decide(req)
                RUNS["requests"] += 1
                self.trace.append({"request": req, "answer": got, "want": None, "probe": True})
                self.check(got.get("accept") is True and got["at"] == len(s.events), "the_creator_can_always_ignore", req, got)
                self.check(got["event"] == M.event_of(req, s.id), "the probe ignore's event", got["event"])
                self.engine.load(s.id, snap["k"], snap["state"])
                EXTRA["the_creator_can_always_ignore: as a probe"] += 1
            got = self.engine.query({"query": "stream", "stream_id": s.id})
            self.check(got == s.read(), "the read after the snapshot is loaded back", got, s.read())

    @invariant()
    def theorems_hold(self):
        for s in self.streams.values():
            if not s.opened:
                self.check(not s.events, "events on a stream never opened")
                continue
            opener = s.opener
            created, advisers, advised, reviewers, reviewed, decided = set(), {}, {}, {}, set(), set()
            for e in s.events:
                name = e["event"]
                if name in ("stream.opened", "stream.closed"):
                    if name == "stream.closed":
                        self.check(e["actor_id"] == opener, "only_the_opener_closes_the_stream")
                        self.check(e is s.events[-1], "nothing_follows_a_close")
                    continue
                k = e["triage_id"]
                if name != "triage.created":
                    self.check(k in created, "every_event_names_a_created_triage")
                self.check(k not in decided, "nothing_follows_a_decision")
                if name == "triage.created":
                    self.check(e["actor_id"] == opener, "every_triage_is_created_by_the_opener")
                    self.check(k not in created, "a_triage_is_created_once")
                    created.add(k)
                elif name == "triage.asked":
                    d = e["adviser_id"]
                    self.check(e["actor_id"] == opener, "every_ask_is_by_the_opener")
                    self.check(d != opener, "no_adviser_is_the_opener")
                    self.check(d not in advisers.setdefault(k, set()), "an_adviser_is_asked_once")
                    self.check(d not in reviewers.get(k, set()), "no_adviser_is_a_reviewer")
                    self.check(k not in reviewed, "nothing_is_asked_or_advised_after_the_review")
                    advisers[k].add(d)
                elif name == "triage.advised":
                    self.check(e["actor_id"] in advisers.get(k, set()), "every_advice_is_by_an_asked_adviser")
                    self.check(e["actor_id"] not in advised.setdefault(k, set()), "an_adviser_advises_once")
                    self.check(k not in reviewed, "nothing_is_asked_or_advised_after_the_review")
                    self.check(e["verdict"] in M.VERDICTS, "a verdict")
                    advised[k].add(e["actor_id"])
                elif name == "triage.reviewed":
                    r = e["actor_id"]
                    self.check(r != opener, "no_reviewer_is_the_opener")
                    self.check(r not in advisers.get(k, set()), "no_adviser_is_a_reviewer")
                    self.check(e["verdict"] in M.VERDICTS, "a verdict")
                    reviewers.setdefault(k, set()).add(r)
                    reviewed.add(k)
                elif name in ("triage.replied", "triage.ignored"):
                    self.check(e["actor_id"] == opener, "the_reply_is_by_the_opener / the_ignore_is_by_the_opener")
                    self.check(k not in decided, "a_triage_is_decided_once")
                    decided.add(k)
                else:
                    self.fail("an event the theorems do not know", name)
            for k in created:
                self.check(not (advisers.get(k, set()) & reviewers.get(k, set())), "roles_are_disjoint")

    @invariant()
    def read_is_the_notes(self):
        for s in self.streams.values():
            got = self.engine.query({"query": "stream", "stream_id": s.id})
            self.check(got == s.read(), "the read is the notes", got, s.read())


EXAMPLES = int(os.environ.get("TRIAGE_EXAMPLES", "400"))
STEPS = int(os.environ.get("TRIAGE_STEPS", "80"))
TestTriage = TriageMachine.TestCase
TestTriage.settings = settings(max_examples=EXAMPLES, stateful_step_count=STEPS, deadline=None, database=None,
                               suppress_health_check=[HealthCheck.too_slow])


def _ran():
    if RUNS["runs"] == 0:
        pytest.skip("the state machine did not run in this session")


def test_coverage_is_complete():
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
    expected.add(("triage.create", "fresh_ids_must_match_the_command"))
    missing = sorted(p for p in expected if SEEN[p] == 0)
    assert not missing, "never observed in %d runs: %s" % (RUNS["runs"], missing)
    unexpected = sorted(p for p in SEEN if p not in expected and p[1] != "accepted")
    assert not unexpected, "observed but not described: %s" % unexpected
    assert EXTRA["the_creator_can_always_ignore: as a rule"] > 0
    assert EXTRA["the_creator_can_always_ignore: as a probe"] > 0


def test_description_is_the_model():
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
