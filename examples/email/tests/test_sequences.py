# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Random command sequences against the compiled email engine (Hypothesis, stateful), with requirements on what the
run must have exercised, so that a pass means something measurable.

On every step of every generated sequence:

1. the engine's answer is the model's (email_model.py: the wire's decoding, the core's admission and the layer's
   fifteen rules in the engine's order): the reason of every refusal, the event and position of every acceptance,
   `malformed` for a request the engine does not decode;
2. the theorems of Email/Theorems.lean hold of the accepted log as invariants;
3. `the_creator_can_always_send` holds right here: for every undecided email on an open stream the engine's state is
   snapshotted, the opener's send at an .eml not yet named is sent and must be accepted, and the snapshot is loaded
   back, after which the stream reads as before;
4. the read of each stream (`{"query": "stream"}`) is the model's notes.

At the end of the run (test_coverage_is_complete, test_deep_states_are_reached) the run must have observed, for every
command the engine describes, every (command, rule) refusal the description lists, an acceptance, and a malformed
request; a wrong number of fresh ids; the acceptance theorem exercised as a rule; and each named deep state of
DEEP_STATES at least once. The counters are printed at exit.

Run from the repository root, with the engine built (`lake build` in examples/email):

    PYTHONPATH=host python3 -m pytest examples/email/tests -q

EMAIL_EXAMPLES and EMAIL_STEPS set the budget (default 400 x 80). EMAIL_ENGINE names another engine (the mutant script
does). A failing sequence is written to .hypothesis/failing.trace.json, shrunk.
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
import email_model as M

ENGINE = os.environ.get("EMAIL_ENGINE") or os.path.join(REPO, "examples", "email", ".lake", "build", "bin", "email-engine")
DUMP_DIR = os.environ.get("EMAIL_DUMP") or os.path.join(HERE, ".hypothesis")
NS = uuid.UUID("12345678-1234-5678-1234-567812345678")


def U(name: str) -> str:
    return str(uuid.uuid5(NS, name))


ANN, BEN, CY, DEE, EVE, FAY = (U(p) for p in ("ann", "ben", "cy", "dee", "eve", "fay"))
PRINCIPALS = [ANN, BEN, CY, DEE, EVE, FAY]
S, T = U("stream-s"), U("stream-t")
STREAMS = [S, T]
EMAILS = [U("email-%d" % i) for i in range(4)]
PROOF_URL = M.PROOF_URL
GOOD_EMLS = ["https://example.org/mail/%s.eml" % x for x in
             ("in0", "in1", "d1", "d2", "d3", "d4", "c1", "c2", "c3", "c4", "c5", "s1", "s2", "s3")]
BAD_EMLS = ["", "no-scheme.eml", "https://", "://host.eml", "https://a b/c.eml", "https://x/\x01y.eml", "a://b://c.eml",
            "https://example.org/mail/not-an-eml", "https://example.org/mail/x.EML"]
BAD_PROOF_URLS = ["https://example.org/provenstream/commit/0123456789abcdef", PROOF_URL.upper(),
                  "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567",
                  "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/../x",
                  "https://example.org/commit/0123456789abcdef0123456789abcdef01234567", "ftp:/x/commit/" + "0" * 40]
SCREENS = ["https://example.org/screens/s%d.svg" % i for i in range(3)]
BAD_URLS = ["", "https://", "https://a b/c"]

# -- what the run exercised: printed at exit, required by the tests at the end of this file -----------------------------

SEEN = collections.Counter()      # (command, outcome): outcome is 'accepted', a reason, or 'malformed'
EXTRA = collections.Counter()     # the acceptance theorem as a rule and as a probe, per step
DEEP = collections.Counter()      # deep state -> runs that reached it
RUNS = collections.Counter()      # runs, steps, requests

# every refusal the engine describes, per command; what aimed_refusal aims at and test_coverage_is_complete requires
TARGETS = [(cmd, r) for cmd in M.COMMANDS for r in M.expected_rules(cmd)] + \
          [(cmd, "malformed") for cmd in M.COMMANDS] + \
          [("stream.open", "fresh_ids_must_match_the_command"), ("email.create", "fresh_ids_must_match_the_command")]

# every pair of layer rules tried on one command, in the engine's order: (command, first, second)
PAIR_TARGETS = [(cmd, a, b) for cmd in M.LAYER for i, a in enumerate(M.rules_of(cmd)) for b in M.rules_of(cmd)[i + 1:]]

DEEP_STATES = ("a send after at least one composed draft", "two composed drafts on one email (a revise round)",
               "two distinct composers on one email", "drafts by two drafters on one email",
               "an email created in reply to a message", "an email created in reply to another email's sent message",
               "a send with no draft and no composed draft", "a close while an email is undecided",
               "both streams open at once")


@atexit.register
def _report():
    if not SEEN:
        return
    print("\nemail sequences: %d runs, %d steps, %d requests" % (RUNS["runs"], RUNS["steps"], RUNS["requests"]),
          file=sys.stderr)
    width = max(len("%s %s" % k) for k in SEEN)
    for (cmd, outcome), n in sorted(SEEN.items(), key=lambda kv: (kv[0][0], -kv[1], kv[0][1])):
        print("  %-*s %7d" % (width, "%s %s" % (cmd, outcome), n), file=sys.stderr)
    for k, n in sorted(EXTRA.items()):
        print("  %-*s %7d" % (width, k, n), file=sys.stderr)
    print("deep states reached (runs):", file=sys.stderr)
    for name in DEEP_STATES:
        print("  %-*s %7d" % (width, name, DEEP[name]), file=sys.stderr)


principals = st.sampled_from(PRINCIPALS)
emails = st.sampled_from(EMAILS)
metas = st.one_of(st.none(), st.text(alphabet=st.characters(min_codepoint=32, max_codepoint=0x7e), max_size=12))


def dump_failing(trace, failure, where):
    os.makedirs(where, exist_ok=True)
    with open(os.path.join(where, "failing.trace.json"), "w", encoding="utf-8") as f:
        json.dump({"failure": [repr(x) for x in failure], "trace": trace}, f, indent=1, default=str)


def deep_states(streams) -> set:
    """The named deep states a run's accepted log reached."""
    reached = set()
    both = False
    for s in streams.values():
        if not s.opened:
            continue
        by_email = collections.defaultdict(list)
        sent_emls = {}
        for e in s.events:
            if "email_id" in e:
                by_email[e["email_id"]].append(e)
            if e["event"] == "email.sent":
                sent_emls[e["sent_url"]] = e["email_id"]
            if e["event"] == "email.created" and e.get("in_reply_to_url") is not None:
                reached.add("an email created in reply to a message")
                if e["in_reply_to_url"] in sent_emls and sent_emls[e["in_reply_to_url"]] != e["email_id"]:
                    reached.add("an email created in reply to another email's sent message")
        for k, evs in by_email.items():
            names = [e["event"] for e in evs]
            if "email.composed" in names and "email.sent" in names and \
                    names.index("email.composed") < names.index("email.sent"):
                reached.add("a send after at least one composed draft")
            if names.count("email.composed") >= 2:
                reached.add("two composed drafts on one email (a revise round)")
            if len({e["actor_id"] for e in evs if e["event"] == "email.composed"}) >= 2:
                reached.add("two distinct composers on one email")
            if len({e["actor_id"] for e in evs if e["event"] == "email.drafted"}) >= 2:
                reached.add("drafts by two drafters on one email")
            if "email.sent" in names and "email.drafted" not in names and "email.composed" not in names:
                reached.add("a send with no draft and no composed draft")
        if s.closed and s.undecided():
            reached.add("a close while an email is undecided")
        both = both or getattr(s, "opened_while_other_open", False)
    if both:
        reached.add("both streams open at once")
    return reached


class EmailMachine(RuleBasedStateMachine):
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
        """`prefer`: 'opener', ('drafter', k), ('composer', k) (a principal who is neither a drafter nor the opener),
        or None for anyone. Four times in five the preferred, else anyone."""
        if stream.opener is not None and prefer is not None and data.draw(st.sampled_from([True] * 4 + [False])):
            if prefer == "opener":
                return stream.opener
            k = prefer[1]
            drafters = stream.drafters(k)
            if prefer[0] == "drafter" and drafters:
                return data.draw(st.sampled_from(drafters))
            if prefer[0] == "composer":
                return self.pick_composer(data, stream, k)
        return data.draw(principals)

    def pick_email(self, data, stream, prefer_undecided=True, ripe=None):
        """Half the time an email `ripe` for the rule (one step from a deep state), else mostly a live one, else any."""
        created = stream.emails()
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
        return data.draw(emails)

    def pick_eml(self, data, stream, k, replying=False):
        """Mostly an .eml not yet named on the email; sometimes one that is; one time in fourteen a bad one; for a
        create, often another email's sent message (a reply to what was sent)."""
        roll = data.draw(st.integers(0, 13))
        if roll == 0:
            return data.draw(st.sampled_from(BAD_EMLS))
        used = stream.emls(k)
        if roll == 1 and used:
            return data.draw(st.sampled_from(used))
        if replying and roll in (2, 3, 4):
            sent = [n[2] for n in stream.notes if n[0] == "sent" and n[1] != k]
            if sent:
                return data.draw(st.sampled_from(sent))
        free = [u for u in GOOD_EMLS if u not in used]
        if free:
            return data.draw(st.sampled_from(free))
        self.fresh_counter += 1
        return "https://example.org/mail/fresh%d.eml" % self.fresh_counter

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
        required = [k for k in f if k not in ("command", "meta", "in_reply_to_url")]
        if how == "upper" and uuids:
            k = data.draw(st.sampled_from(uuids))
            f[k] = f[k].upper()
        elif how == "missing" and required:
            del f[data.draw(st.sampled_from(required))]
        else:
            f["extra"] = 1
        return f

    def life(self, stream, k):
        """How many events the email has: decisions are held back on a young email so that work accumulates."""
        return sum(1 for e in stream.events if e.get("email_id") == k)

    def fresh_drafter(self, stream, k):
        return [p for p in PRINCIPALS if p != stream.opener and p not in stream.drafters(k)
                and p not in stream.composers(k)]

    def pick_drafter(self, data, stream, k):
        """Five times in eight someone the opener may solicit (not the opener, not yet a drafter or composer of k);
        else, deliberately, the opener, a drafter already solicited, or a composer of the email."""
        if stream.opener is None:
            return data.draw(principals)
        roll = data.draw(st.integers(0, 7))
        if roll == 0:
            return stream.opener
        if roll == 1 and stream.drafters(k):
            return data.draw(st.sampled_from(stream.drafters(k)))
        if roll == 2 and stream.composers(k):
            return data.draw(st.sampled_from(stream.composers(k)))
        fresh = self.fresh_drafter(stream, k)
        return data.draw(st.sampled_from(fresh)) if fresh else data.draw(principals)

    def pick_composer(self, data, stream, k):
        """Someone who may compose: neither the opener nor a drafter of the email. Two times in three one who has
        composed k already, so that composing does not use up the principals the opener could still solicit (a
        composer is never afterwards a drafter of the email); scenario_two_composers brings in the second."""
        able = [p for p in PRINCIPALS if p != stream.opener and p not in stream.drafters(k)]
        again = [p for p in able if p in stream.composers(k)]
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
        k = data.draw(emails)
        f = {"command": "email.create", "stream_id": sid, "email_id": k}
        # the optional message replied to: absent a third of the time, else null, a message, or (one time in twelve) a bad URL
        roll = data.draw(st.integers(0, 11))
        if roll == 0:
            f["in_reply_to_url"] = None
        elif roll in (1, 2, 3, 4, 5, 6):
            f["in_reply_to_url"] = self.pick_eml(data, stream, k, replying=True)
        elif roll == 7:
            f["in_reply_to_url"] = data.draw(st.sampled_from(BAD_EMLS))
        fresh = [U("extra")] if data.draw(st.integers(0, 19)) == 0 else []
        self.send(actor, self.mangle(data, self.with_meta(data, f)), fresh)

    @rule(data=st.data())
    def solicit(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        actor = self.pick_actor(data, stream, "opener")
        # ripe: one drafter already, not composed: a second drafter can be solicited
        k = self.pick_email(data, stream, ripe=lambda k: len(stream.drafters(k)) == 1 and not stream.composed(k))
        d = self.pick_drafter(data, stream, k)
        f = {"command": "email.solicit", "stream_id": sid, "email_id": k, "drafter_id": d}
        self.send(actor, self.mangle(data, self.with_meta(data, f)))

    @rule(data=st.data())
    def draft(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        decided = [k for k in stream.emails() if stream.decided(k) and not stream.composed(k)]
        if decided and data.draw(st.integers(0, 7)) == 0:
            k = data.draw(st.sampled_from(decided))         # a draft after the decision: refused
        else:
            k = self.pick_email(data, stream)
        actor = self.pick_actor(data, stream, ("drafter", k))
        f = {"command": "email.draft", "stream_id": sid, "email_id": k, "draft_url": self.pick_eml(data, stream, k)}
        self.send(actor, self.mangle(data, self.with_meta(data, f)))

    @rule(data=st.data())
    def compose(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        k = self.pick_email(data, stream)
        actor = self.pick_actor(data, stream, ("composer", k))
        drafters = stream.drafters(k)
        if drafters and data.draw(st.sampled_from([False] * 7 + [True])):
            actor = data.draw(st.sampled_from(drafters))            # a drafter composing its own email: refused
        if self.life(stream, k) < 2 and data.draw(st.sampled_from([True] * 2 + [False])):
            return                                                   # let drafts accumulate before the cutoff
        sc = data.draw(st.sampled_from(SCREENS * 4 + BAD_URLS[:1]))
        f = {"command": "email.compose", "stream_id": sid, "email_id": k,
             "composed_url": self.pick_eml(data, stream, k), "screen_url": sc}
        self.send(actor, self.mangle(data, self.with_meta(data, f)))

    @rule(data=st.data())
    def send_email(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        actor = self.pick_actor(data, stream, "opener")
        k = self.pick_email(data, stream, prefer_undecided=False)
        hold = 5 if self.life(stream, k) < 8 else 1
        if data.draw(st.sampled_from([True] * hold + [False])):
            return
        f = {"command": "email.send", "stream_id": sid, "email_id": k, "sent_url": self.pick_eml(data, stream, k)}
        self.send(actor, self.mangle(data, self.with_meta(data, f)))

    @rule(data=st.data())
    def discard(self, data):
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        actor = self.pick_actor(data, stream, "opener")
        k = self.pick_email(data, stream, prefer_undecided=False)
        hold = 7 if self.life(stream, k) < 8 else 1
        if data.draw(st.sampled_from([True] * hold + [False])):
            return
        self.send(actor, self.mangle(data, self.with_meta(data, {"command": "email.discard", "stream_id": sid, "email_id": k})))

    # ---- scenarios: a few valid steps on one email in one rule, so that the deep states are reached ----
    # Every request still goes through `send`, so each is predicted by the model and checked against the engine.

    def live_email(self, data, stream, ripe):
        """An undecided email `ripe` for the scenario, else None."""
        good = [k for k in stream.undecided() if ripe(k)] if stream.opened and not stream.closed else []
        return data.draw(st.sampled_from(good)) if good else None

    def layer(self, data, actor, cmd, stream, k, **fields):
        f = {"command": cmd, "stream_id": stream.id, "email_id": k}
        f.update(fields)
        return self.send(actor, self.with_meta(data, f))

    @rule(data=st.data())
    def scenario_second_drafter_drafts(self, data):
        """On an email with one drafter who has drafted, the opener solicits another, and both draft."""
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        k = self.live_email(data, stream, lambda k: not stream.composed(k) and len(stream.drafters(k)) <= 2)
        if k is None:
            return
        drafters = stream.drafters(k)
        if len(drafters) < 2:
            fresh = self.fresh_drafter(stream, k)
            if not fresh:
                return
            d = data.draw(st.sampled_from(fresh))
            self.layer(data, stream.opener, "email.solicit", stream, k, drafter_id=d)
            drafters = stream.drafters(k)
        for d in drafters[-2:]:
            self.layer(data, d, "email.draft", stream, k, draft_url=self.unnamed(data, stream, k))

    @rule(data=st.data())
    def scenario_two_composers(self, data):
        """Two distinct composers each hand in a final draft and a screen on one email."""
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        k = self.live_email(data, stream, lambda k: len(set(stream.composers(k))) <= 1)
        if k is None:
            return
        able = [p for p in PRINCIPALS if p != stream.opener and p not in stream.drafters(k) and p not in stream.composers(k)]
        for r in able[:2]:
            self.layer(data, r, "email.compose", stream, k, composed_url=self.unnamed(data, stream, k),
                       screen_url=data.draw(st.sampled_from(SCREENS)))

    @rule(data=st.data())
    def scenario_revise(self, data):
        """A drafted email is composed, and composed again by the same composer (a revise round), with drafting cut
        off in between."""
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        k = self.live_email(data, stream, lambda k: True)
        if k is None:
            return
        if not stream.drafters(k) and not stream.composed(k):
            fresh = self.fresh_drafter(stream, k)
            if fresh:
                d = data.draw(st.sampled_from(fresh))
                self.layer(data, stream.opener, "email.solicit", stream, k, drafter_id=d)
                self.layer(data, d, "email.draft", stream, k, draft_url=self.unnamed(data, stream, k))
        r = self.pick_composer(data, stream, k)
        self.layer(data, r, "email.compose", stream, k, composed_url=self.unnamed(data, stream, k),
                   screen_url=data.draw(st.sampled_from(SCREENS)))
        fresh = self.fresh_drafter(stream, k)
        if fresh:
            self.layer(data, stream.opener, "email.solicit", stream, k, drafter_id=data.draw(st.sampled_from(fresh)))
        self.layer(data, r, "email.compose", stream, k, composed_url=self.unnamed(data, stream, k),
                   screen_url=data.draw(st.sampled_from(SCREENS)))

    @rule(data=st.data())
    def scenario_compose_then_send(self, data):
        """An email with work on it is composed and sent, and a reply to what was sent is created."""
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        k = self.live_email(data, stream, lambda k: self.life(stream, k) >= 2)
        if k is None:
            return
        if not stream.composers(k):
            self.layer(data, self.pick_composer(data, stream, k), "email.compose", stream, k,
                       composed_url=self.unnamed(data, stream, k), screen_url=data.draw(st.sampled_from(SCREENS)))
        out = self.unnamed(data, stream, k)
        self.layer(data, stream.opener, "email.send", stream, k, sent_url=out)
        new = [c for c in EMAILS if not stream.noted("email", c)]
        if new and data.draw(st.sampled_from([True] * 2 + [False])):
            self.layer(data, stream.opener, "email.create", stream, data.draw(st.sampled_from(new)), in_reply_to_url=out)

    @rule(data=st.data())
    def scenario_decided_before_any_compose(self, data):
        """An email with a solicited drafter is decided before anything is composed; the drafter's draft and a further
        solicitation then meet email_must_be_undecided, which needs exactly this state (a compose would answer first
        with email_must_not_be_composed)."""
        if data.draw(st.sampled_from([True] * 3 + [False])):
            return
        sid = self.pick_stream(data)
        stream = self.streams[sid]
        k = self.live_email(data, stream, lambda k: not stream.composed(k))
        if k is None:
            return
        if not stream.drafters(k):
            fresh = self.fresh_drafter(stream, k)
            if not fresh:
                return
            self.layer(data, stream.opener, "email.solicit", stream, k, drafter_id=data.draw(st.sampled_from(fresh)))
            if not stream.drafters(k):      # with_meta made the solicitation malformed: nothing to go on with
                return
        if data.draw(st.booleans()):
            self.layer(data, stream.opener, "email.send", stream, k, sent_url=self.unnamed(data, stream, k))
        else:
            self.layer(data, stream.opener, "email.discard", stream, k)
        self.layer(data, data.draw(st.sampled_from(stream.drafters(k))), "email.draft", stream, k, draft_url=self.unnamed(data, stream, k))
        fresh = self.fresh_drafter(stream, k)
        if fresh:
            self.layer(data, stream.opener, "email.solicit", stream, k, drafter_id=data.draw(st.sampled_from(fresh)))

    # ---- refusals, aimed: a request built to meet one named rule, the target drawn by Hypothesis ----
    # Each (command, reason) the engine describes is a target. The construction says how the rule is reached; the model
    # still judges the request, so a construction that misses is a refusal for another reason, or an acceptance, and
    # is checked like any other request.

    def form(self, data, cmd, stream, k=None, url=None, drafter=None):
        f = {"command": cmd}
        if cmd == "stream.open":
            f["proof_revision_url"] = url or PROOF_URL
            return f
        f["stream_id"] = stream.id
        if cmd == "stream.close":
            return f
        f["email_id"] = k
        if cmd in M.EML_FIELD and cmd != "email.create":
            f[M.EML_FIELD[cmd]] = url or self.unnamed(data, stream, k)
        if cmd == "email.solicit":
            fresh = self.fresh_drafter(stream, k)
            f["drafter_id"] = drafter or (data.draw(st.sampled_from(fresh)) if fresh else data.draw(principals))
        if cmd == "email.compose":
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
        # the open stream with undecided emails, when there is one: most targets need an email to be about
        s = pick([x for x in opened if x.undecided()] or opened) or self.streams[S]
        k0 = pick(s.emails()) or EMAILS[0]
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
            return (data.draw(principals), self.form(data, cmd, t, EMAILS[0]), []) if t else None
        if not opened:
            return None
        if cmd == "stream.close":
            return (pick(others), self.form(data, cmd, s), [])
        if reason not in ("only_opener_can_create", "email_id_must_be_new", "email_must_exist") and not s.undecided():
            unused = [c for c in EMAILS if not s.noted("email", c)]  # set up: most targets need a live email
            if unused:
                self.send(s.opener, self.form(data, "email.create", s, pick(unused)), [])
        live = s.undecided()
        new = [c for c in EMAILS if not s.noted("email", c)]
        decided = [k for k in s.emails() if s.decided(k)]
        uncomposed = lambda ks: [k for k in ks if not s.composed(k)]
        if reason == "only_opener_can_create":
            return (pick(others), self.form(data, cmd, s, pick(new) or k0), [])
        if reason == "email_id_must_be_new":
            k = pick(s.emails())
            return (s.opener, self.form(data, cmd, s, k), []) if k else None
        if reason == "email_must_exist":
            k = pick(new)
            actor = pick(others) if cmd in ("email.draft", "email.compose") else s.opener
            return (actor, self.form(data, cmd, s, k), []) if k else None
        if reason == "eml_urls_must_be_unique":
            k = pick(k for k in live if s.emls(k))
            if k is None:
                return None
            url = pick(s.emls(k))
            actor = {"email.send": s.opener,
                     "email.draft": pick(s.drafters(k)),
                     "email.compose": pick(p for p in others if p not in s.drafters(k))}[cmd]
            return (actor, self.form(data, cmd, s, k, url=url), []) if actor else None
        if reason == "only_opener_can_solicit":
            k = pick(live)
            return (pick(others), self.form(data, cmd, s, k), []) if k else None
        if reason == "drafter_must_not_be_the_opener":
            k = pick(live)
            return (s.opener, self.form(data, cmd, s, k, drafter=s.opener), []) if k else None
        if reason == "drafter_is_solicited_once":
            k = pick(k for k in uncomposed(live) if s.drafters(k))
            return (s.opener, self.form(data, cmd, s, k, drafter=pick(s.drafters(k))), []) if k else None
        if reason == "drafter_must_not_be_a_composer":
            k = pick(k for k in live if set(s.composers(k)) - set(s.drafters(k)))
            if k is None:
                return None
            return (s.opener, self.form(data, cmd, s, k, drafter=pick(set(s.composers(k)) - set(s.drafters(k)))), [])
        if reason == "email_must_not_be_composed":
            k = pick(k for k in live if s.composed(k) and (cmd == "email.solicit" and self.fresh_drafter(s, k)
                                                            or cmd == "email.draft" and s.drafters(k)))
            if k is None:
                return None
            actor = s.opener if cmd == "email.solicit" else pick(s.drafters(k))
            return (actor, self.form(data, cmd, s, k), [])
        if reason == "only_solicited_drafters_can_draft":
            k = pick(uncomposed(live))
            return (pick(p for p in PRINCIPALS if p not in s.drafters(k)), self.form(data, cmd, s, k), []) if k else None
        if reason == "composer_must_not_be_a_drafter":
            k = pick(k for k in live if s.drafters(k))
            return (pick(s.drafters(k)), self.form(data, cmd, s, k), []) if k else None
        if reason == "composer_must_not_be_the_opener":
            k = pick(live)
            return (s.opener, self.form(data, cmd, s, k), []) if k else None
        if reason == "only_opener_can_decide":
            k = pick(live)
            return (pick(others), self.form(data, cmd, s, k), []) if k else None
        if reason == "email_is_decided_once":
            k = pick(decided)
            return (s.opener, self.form(data, cmd, s, k), []) if k else None
        if reason == "email_must_be_undecided":
            if cmd == "email.compose":
                k = pick(decided)
                actor = pick(p for p in others if p not in s.drafters(k)) if k else None
            elif cmd == "email.solicit":
                k = pick(k for k in uncomposed(decided) if self.fresh_drafter(s, k))
                actor = s.opener
            else:
                k = pick(k for k in uncomposed(decided) if s.drafters(k))
                actor = pick(s.drafters(k)) if k else None
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
    # engine's order is the one that must answer ----

    def violate(self, data, s, cmd, reasons):
        """`(actor, command, [])` that breaks every rule in `reasons` (all of `cmd`), built from stream `s`: an email
        meeting each rule's condition, the valid actor and fields, then each rule's violation applied. None when the
        state has no such email or the violations conflict."""
        def pick(xs):
            xs = list(xs)
            return data.draw(st.sampled_from(xs)) if xs else None
        if s.opener is None or s.closed:
            return None
        others = [p for p in PRINCIPALS if p != s.opener]
        conds = {"email_id_must_be_new": lambda k: s.noted("email", k),
                 "email_must_exist": lambda k: not s.noted("email", k),
                 "eml_urls_must_be_unique": lambda k: s.emls(k),
                 "drafter_is_solicited_once": lambda k: s.drafters(k),
                 "drafter_must_not_be_a_composer": lambda k: set(s.composers(k)) - set(s.drafters(k)),
                 "email_must_not_be_composed": lambda k: s.composed(k),
                 "composer_must_not_be_a_drafter": lambda k: s.drafters(k),
                 "email_is_decided_once": lambda k: s.decided(k),
                 "email_must_be_undecided": lambda k: s.decided(k)}
        ks = [k for k in EMAILS if all(conds[r](k) for r in reasons if r in conds)]
        if "email_must_exist" not in reasons:
            ks = [k for k in ks if s.noted("email", k)]
        k = pick(ks)
        if k is None:
            return None
        f = self.form(data, cmd, s, k)
        actor = {"email.draft": pick(s.drafters(k)),
                 "email.compose": pick(p for p in others if p not in s.drafters(k))}.get(cmd, s.opener)
        if cmd == "email.solicit":
            fresh = self.fresh_drafter(s, k)
            f["drafter_id"] = pick(fresh) or data.draw(principals)
        for r in reasons:
            if r in ("only_opener_can_create", "only_opener_can_solicit", "only_opener_can_decide",
                     "composer_must_not_be_the_opener"):
                actor = s.opener if r == "composer_must_not_be_the_opener" else pick(others)
            elif r == "only_solicited_drafters_can_draft":
                actor = pick(p for p in PRINCIPALS if p not in s.drafters(k))
            elif r == "composer_must_not_be_a_drafter":
                actor = pick(s.drafters(k))
            elif r == "eml_urls_must_be_unique":
                f[M.EML_FIELD[cmd]] = pick(s.emls(k))
            elif r == "drafter_must_not_be_the_opener":
                f["drafter_id"] = s.opener
            elif r == "drafter_is_solicited_once":
                f["drafter_id"] = pick(s.drafters(k))
            elif r == "drafter_must_not_be_a_composer":
                f["drafter_id"] = pick(set(s.composers(k)) - set(s.drafters(k)))
        if actor is None or f.get("drafter_id") is None and cmd == "email.solicit":
            return None
        return (actor, f, [])

    @rule(data=st.data())
    def aimed_pair(self, data):
        start = data.draw(st.integers(0, len(PAIR_TARGETS) - 1)) + self.steps
        opened = [x for x in self.streams.values() if x.opened and not x.closed and x.emails()]
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
        free = [u for u in GOOD_EMLS if not stream.eml_named(k, u)]
        if free and data is not None:
            return data.draw(st.sampled_from(free))
        self.fresh_counter += 1
        return "https://example.org/mail/fresh%d.eml" % self.fresh_counter

    @precondition(lambda self: bool(self.undecided()))
    @rule(data=st.data())
    def the_creator_can_always_send(self, data):
        """Whatever happened before: an undecided email on an open stream, an .eml not yet named on it, the opener's
        send is accepted."""
        if data.draw(st.sampled_from([True] * 3 + [False])):
            return
        stream, k = data.draw(st.sampled_from(self.undecided()))
        f = {"command": "email.send", "stream_id": stream.id, "email_id": k, "sent_url": self.unnamed(data, stream, k)}
        got = self.send(stream.opener, f)
        self.check(got.get("accept") is True, "the_creator_can_always_send", got)
        EXTRA["the_creator_can_always_send: as a rule"] += 1

    # ---- the acceptance theorem, at every step ----

    @invariant()
    def the_creator_can_always_send_everywhere(self):
        """After every step: for each undecided email on an open stream, the opener's send at an unnamed .eml is
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
                       "command": {"command": "email.send", "stream_id": s.id, "email_id": k, "sent_url": u}}
                self.check(M.judge(s, req) is None, "the model must accept the opener's send", req)
                got = self.engine.decide(req)
                RUNS["requests"] += 1
                self.trace.append({"request": req, "answer": got, "want": None, "probe": True})
                self.check(got.get("accept") is True and got["at"] == len(s.events), "the_creator_can_always_send",
                           req, got)
                self.check(got["event"] == M.event_of(req, s.id), "the probe send's event", got["event"])
                self.engine.load(s.id, snap["k"], snap["state"])
                EXTRA["the_creator_can_always_send: as a probe"] += 1
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
            created, drafters, composers, composed, decided = set(), {}, {}, set(), set()
            emls = {}
            for e in s.events:
                name = e["event"]
                if name in ("stream.opened", "stream.closed"):
                    if name == "stream.closed":
                        self.check(e["actor_id"] == opener, "only_the_opener_closes_the_stream")
                        self.check(e is s.events[-1], "nothing_follows_a_close")
                    continue
                k = e["email_id"]
                if name != "email.created":
                    self.check(k in created, "every_event_names_a_created_email")
                self.check(k not in decided, "nothing_follows_a_decision")
                field = {"email.created": "in_reply_to_url", "email.drafted": "draft_url",
                         "email.composed": "composed_url", "email.sent": "sent_url"}.get(name)
                if field and e.get(field) is not None:
                    self.check(e[field] not in emls.setdefault(k, set()), "emls_are_distinct")
                    emls[k].add(e[field])
                if name == "email.created":
                    self.check(e["actor_id"] == opener, "every_email_is_created_by_the_opener")
                    self.check(k not in created, "an_email_is_created_once")
                    created.add(k)
                elif name == "email.solicited":
                    d = e["drafter_id"]
                    self.check(e["actor_id"] == opener, "every_solicitation_is_by_the_opener")
                    self.check(d != opener, "no_drafter_is_the_opener")
                    self.check(d not in drafters.setdefault(k, set()), "a_drafter_is_solicited_once")
                    self.check(d not in composers.get(k, set()), "no_drafter_is_a_composer")
                    self.check(k not in composed, "nothing_is_solicited_or_drafted_after_the_compose")
                    drafters[k].add(d)
                elif name == "email.drafted":
                    self.check(e["actor_id"] in drafters.get(k, set()), "every_draft_is_by_a_solicited_drafter")
                    self.check(k not in composed, "nothing_is_solicited_or_drafted_after_the_compose")
                elif name == "email.composed":
                    r = e["actor_id"]
                    self.check(r != opener, "no_composer_is_the_opener")
                    self.check(r not in drafters.get(k, set()), "no_drafter_is_a_composer")
                    composers.setdefault(k, set()).add(r)
                    composed.add(k)
                elif name in ("email.sent", "email.discarded"):
                    self.check(e["actor_id"] == opener, "the_send_is_by_the_opener / the_discard_is_by_the_opener")
                    self.check(k not in decided, "an_email_is_decided_once")
                    decided.add(k)
                else:
                    self.fail("an event the theorems do not know", name)
            for k in created:
                self.check(not (drafters.get(k, set()) & composers.get(k, set())), "roles_are_disjoint")

    @invariant()
    def read_is_the_notes(self):
        for s in self.streams.values():
            got = self.engine.query({"query": "stream", "stream_id": s.id})
            self.check(got == s.read(), "the read is the notes", got, s.read())


EXAMPLES = int(os.environ.get("EMAIL_EXAMPLES", "400"))
STEPS = int(os.environ.get("EMAIL_STEPS", "80"))
TestEmail = EmailMachine.TestCase
TestEmail.settings = settings(max_examples=EXAMPLES, stateful_step_count=STEPS, deadline=None, database=None,
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
    expected.add(("email.create", "fresh_ids_must_match_the_command"))
    missing = sorted(p for p in expected if SEEN[p] == 0)
    assert not missing, "never observed in %d runs: %s" % (RUNS["runs"], missing)
    unexpected = sorted(p for p in SEEN if p not in expected and p[1] != "accepted")
    assert not unexpected, "observed but not described: %s" % unexpected
    assert EXTRA["the_creator_can_always_send: as a rule"] > 0, "the acceptance theorem never fired as a rule"
    assert EXTRA["the_creator_can_always_send: as a probe"] > 0, "the acceptance theorem was never probed"


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
