# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Random command sequences against the compiled email-triage-and-reply engine (Hypothesis, stateful), with
requirements on what the run must have exercised. The shape follows examples/email/tests/test_sequences.py.

Requests are built by search. For a command, the machine lists candidate requests from the current state: every
principal as the actor, every item on the stream and one new, and a few values per field. The model judges each
candidate. A step then sends one the model accepts, or one it refuses for a drawn rule. Every request still goes to
the engine, whose answer must be the model's.

On every step of every generated sequence:

1. the engine's answer is the model's (mailbox_model.py): the reason of every refusal, the event and position of every
   acceptance, `malformed` for a request the engine does not decode;
2. the theorems of EmailTriageAndReply/Theorems.lean hold of the accepted log as invariants;
3. the acceptance theorems hold right here. For every undecided email and triage on an open stream, the engine's state
   is snapshotted. The owner's send, ignore, defer and reply must each be accepted, and so must a person delegate's
   send. The snapshot is loaded back after each probe;
4. the read of each stream (`{"query": "stream"}`) is the model's notes.

At the end the run must have observed every (command, rule) refusal the engine describes, an acceptance and a
malformed request per command, a wrong number of fresh ids, each acceptance theorem, and each named deep state.

    PYTHONPATH=host python3 -m pytest examples/email-triage-and-reply/tests -q

MAILBOX_EXAMPLES and MAILBOX_STEPS set the budget (default 300 x 60). MAILBOX_ENGINE names another engine.
"""
from __future__ import annotations
import atexit, collections, json, os, random, sys, uuid

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(REPO, "host"))
sys.path.insert(0, HERE)

import pytest
from hypothesis import HealthCheck, settings, strategies as st
from hypothesis.stateful import RuleBasedStateMachine, initialize, invariant, precondition, rule

from provenstream.engine import Engine
import mailbox_model as M

ENGINE = os.environ.get("MAILBOX_ENGINE") or os.path.join(REPO, "examples", "email-triage-and-reply", ".lake", "build",
                                                          "bin", "email-triage-and-reply-engine")
DUMP_DIR = os.environ.get("MAILBOX_DUMP") or os.path.join(HERE, ".hypothesis")
NS = uuid.UUID("12345678-1234-5678-1234-567812345678")


def U(name: str) -> str:
    return str(uuid.uuid5(NS, name))


ANN, BEN, CY, DEE, EVE, FAY, GUS, HAL = (U(p) for p in ("ann", "ben", "cy", "dee", "eve", "fay", "gus", "hal"))
PRINCIPALS = [ANN, BEN, CY, DEE, EVE, FAY, GUS, HAL]
S, T, NEVER = U("stream-s"), U("stream-t"), U("stream-never")
STREAMS = [S, T, NEVER]
EMAILS = [U("email-%d" % i) for i in range(5)]
TRIAGES = [U("triage-%d" % i) for i in range(4)]
WORK_ITEMS = ["80000000-0000-7000-8000-00000000000%d" % i for i in range(1, 4)]
PROOF_URL = M.PROOF_URL
GOOD_EMLS = ["https://example.org/mail/%s.eml" % x for x in ("in0", "d1", "d2", "d3", "d4", "s1", "s2", "s3")]
MESSAGES = ["eloquentmail://personal/m%d.eml" % i for i in range(4)]
PREPS = ["https://example.org/prep/p%d" % i for i in range(3)]
SCREENS = ["https://example.org/screens/s%d.svg" % i for i in range(2)]
BAD_PROOF_URLS = ["https://example.org/provenstream/commit/0123456789abcdef", PROOF_URL.upper()]
TERMINALS = ("email.send", "email.discard", "triage.reply", "triage.work", "triage.ignore", "triage.defer")

SEEN = collections.Counter()      # (command, outcome): outcome is 'accepted', a reason, or 'malformed'
EXTRA = collections.Counter()     # the acceptance theorems as rules and as probes
DEEP = collections.Counter()      # deep state -> runs that reached it
RUNS = collections.Counter()      # runs, steps, requests

TARGETS = [(cmd, r) for cmd in M.COMMANDS for r in M.expected_rules(cmd)] + \
          [(cmd, "malformed") for cmd in M.COMMANDS] + \
          [("stream.open", "fresh_ids_must_match_the_command"), ("email.create", "fresh_ids_must_match_the_command"),
           ("triage.request", "fresh_ids_must_match_the_command")]
PAIR_TARGETS = [(cmd, a, b) for cmd in M.LAYER for i, a in enumerate(M.rules_of(cmd)) for b in M.rules_of(cmd)[i + 1:]]
ACCEPTANCE = ("the_creator_can_always_send", "the_creator_can_always_ignore", "the_creator_can_always_defer",
              "the_creator_can_always_reply")

DEEP_STATES = (
    "an email created by a delegate", "a triage requested by a delegate", "a principal declared by a delegate",
    "a draft by an agent delegate", "a draft by the owner", "a consideration by an agent delegate",
    "a send by a person delegate", "a terminal decision by a person delegate on a triage",
    "a delegate of a person other than the opener", "a solicitation after a draft", "a preparation after a draft",
    "an ask after a consideration", "advice after a consideration", "two drafters on one email",
    "two considerers on one triage", "advice that disagrees", "a deferral", "a triage replied with an email of the stream",
    "an email created in reply to a triaged message", "a close while an item is undecided", "both streams open at once")


@atexit.register
def _report():
    if not SEEN:
        return
    print("\nemail-triage-and-reply sequences: %d runs, %d steps, %d requests"
          % (RUNS["runs"], RUNS["steps"], RUNS["requests"]), file=sys.stderr)
    width = max(len("%s %s" % k) for k in SEEN)
    for (cmd, outcome), n in sorted(SEEN.items(), key=lambda kv: (kv[0][0] or "", -kv[1], kv[0][1])):
        print("  %-*s %7d" % (width, "%s %s" % (cmd, outcome), n), file=sys.stderr)
    for k, n in sorted(EXTRA.items()):
        print("  %-*s %7d" % (width, k, n), file=sys.stderr)
    print("deep states reached (runs):", file=sys.stderr)
    for name in DEEP_STATES:
        print("  %-*s %7d" % (width, name, DEEP[name]), file=sys.stderr)


metas = st.one_of(st.none(), st.text(alphabet=st.characters(min_codepoint=32, max_codepoint=0x7e), max_size=8))


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
        opener, delegator, invited = s.opener, {}, set()
        by_email, by_triage = collections.defaultdict(list), collections.defaultdict(list)
        drafted, considered, messages, replied_emails = set(), set(), set(), set()
        for e in s.events:
            name, a = e["event"], e.get("actor_id")
            delegate = a != opener and delegator.get(a) == opener
            if name == "principal.delegated":
                delegator[e["delegate_id"]] = a
                if a != opener:
                    reached.add("a delegate of a person other than the opener")
            if name == "principal.invited":
                invited.add(e["principal_id"])
            if name in ("principal.invited", "principal.summoned") and delegate:
                reached.add("a principal declared by a delegate")
            if name.startswith("email."):
                k = e["email_id"]
                by_email[k].append(e)
                if name == "email.created":
                    if delegate:
                        reached.add("an email created by a delegate")
                    if e.get("in_reply_to_eml_url") in messages:
                        reached.add("an email created in reply to a triaged message")
                if name == "email.drafted":
                    if delegate and a not in invited:
                        reached.add("a draft by an agent delegate")
                    if a == opener:
                        reached.add("a draft by the owner")
                    drafted.add(k)
                if name == "email.solicited" and k in drafted:
                    reached.add("a solicitation after a draft")
                if name == "email.prepared" and k in drafted:
                    reached.add("a preparation after a draft")
                if name == "email.sent" and delegate:
                    reached.add("a send by a person delegate")
            if name.startswith("triage."):
                k = e["triage_id"]
                by_triage[k].append(e)
                if name == "triage.requested":
                    messages.add(e["message_eml_url"])
                    if delegate:
                        reached.add("a triage requested by a delegate")
                if name == "triage.considered":
                    if delegate and a not in invited:
                        reached.add("a consideration by an agent delegate")
                    considered.add(k)
                if name == "triage.asked" and k in considered:
                    reached.add("an ask after a consideration")
                if name == "triage.advised" and k in considered:
                    reached.add("advice after a consideration")
                if name in ("triage.replied", "triage.worked", "triage.ignored", "triage.deferred") and delegate:
                    reached.add("a terminal decision by a person delegate on a triage")
                if name == "triage.deferred":
                    reached.add("a deferral")
                if name == "triage.replied":
                    reached.add("a triage replied with an email of the stream")
        for evs in by_email.values():
            if len({e["actor_id"] for e in evs if e["event"] == "email.drafted"}) >= 2:
                reached.add("two drafters on one email")
        for evs in by_triage.values():
            if len({e["actor_id"] for e in evs if e["event"] == "triage.considered"}) >= 2:
                reached.add("two considerers on one triage")
            if len({e["verdict"] for e in evs if e["event"] == "triage.advised"}) >= 2:
                reached.add("advice that disagrees")
        if s.closed and (s.undecided_emails() or s.undecided_triages()):
            reached.add("a close while an item is undecided")
        both = both or getattr(s, "opened_while_other_open", False)
    if both:
        reached.add("both streams open at once")
    return reached


class MailboxMachine(RuleBasedStateMachine):
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

    # ---- candidates: the requests a command could be, from this state ----

    def unnamed(self, s, k):
        free = [u for u in GOOD_EMLS if not s.eml_named(k, u)]
        if free:
            return free[0]
        self.fresh_counter += 1
        return "https://example.org/mail/fresh%d.eml" % self.fresh_counter

    def items(self, s, cmd):
        if cmd.startswith("email."):
            new = [k for k in EMAILS if not s.noted("email", k)]
            return s.emails() + new[:1]
        new = [k for k in TRIAGES if not s.noted("triage", k)]
        return s.triages() + new[:1]

    def field_options(self, s, cmd, k):
        """The values of the command's fields beyond its stream and item, a few per field."""
        if cmd in ("principal.invite", "principal.summon"):
            return [{"principal_id": p} for p in PRINCIPALS]
        if cmd == "principal.delegate":
            return [{"delegate_id": p} for p in PRINCIPALS]
        if cmd == "email.create":
            sent = [n[2] for n in s.notes if n[0] == "sent"]
            msgs = [n[2] for n in s.notes if n[0] == "triage"]
            return [{}, {"in_reply_to_eml_url": GOOD_EMLS[0]}] + \
                [{"in_reply_to_eml_url": u} for u in (sent[:1] + msgs[:1])]
        if cmd == "email.solicit":
            return [{"preparer_id": p} for p in PRINCIPALS]
        if cmd == "email.prepare":
            return [{"preparation_url": PREPS[self.steps % len(PREPS)]}]
        if cmd in ("email.draft", "email.send"):
            field = M.EML_FIELD[cmd]
            opts = [self.unnamed(s, k)] + s.emls(k)[:1]
            out = [{field: u} for u in opts]
            if cmd == "email.draft":
                for f in out:
                    f["screen_url"] = SCREENS[self.steps % len(SCREENS)]
            return out
        if cmd == "triage.request":
            return [{"message_eml_url": MESSAGES[self.steps % len(MESSAGES)]}]
        if cmd == "triage.ask":
            return [{"adviser_id": p} for p in PRINCIPALS]
        if cmd in ("triage.advise", "triage.consider"):
            return [{"verdict": v} for v in M.VERDICTS]
        if cmd == "triage.reply":
            unclaimed, claimed = s.unclaimed_emails(), [e for e in s.emails() if s.reply_claimed(e)]
            new = [e for e in EMAILS if not s.noted("email", e)]
            return [{"email_id": e} for e in unclaimed[:2] + claimed[:1] + new[:1]]
        if cmd == "triage.work":
            return [{"work_id": WORK_ITEMS[self.steps % len(WORK_ITEMS)]}]
        return [{}]

    def candidates(self, s, cmd):
        """Every `(actor, command, fresh)` for `cmd` on stream `s`, well formed."""
        out = []
        if cmd == "stream.open":
            for url in [PROOF_URL] + BAD_PROOF_URLS[:1]:
                out += [(a, {"command": cmd, "proof_revision_url": url}, [s.id]) for a in PRINCIPALS]
            return out
        if cmd == "stream.close":
            return [(a, {"command": cmd, "stream_id": s.id}, []) for a in PRINCIPALS]
        key = "email_id" if cmd.startswith("email.") else "triage_id" if cmd.startswith("triage.") else None
        for k in (self.items(s, cmd) if key else [None]):
            for extra in self.field_options(s, cmd, k):
                f = {"command": cmd, "stream_id": s.id}
                if key:
                    f[key] = k
                f.update(extra)
                out += [(a, dict(f), []) for a in PRINCIPALS]
        return out

    def judge(self, s, cand):
        actor, cmd, fresh = cand
        return M.judge(s, {"actor_id": actor, "command": cmd, "fresh": fresh})

    def with_meta(self, data, f):
        m = data.draw(metas)
        if m is not None:
            f["meta"] = m
        return f

    def mangle(self, rng, f):
        """A command the engine will not decode: an id not in canonical form, an unknown key, a required field missing."""
        f = dict(f)
        how = rng.choice(["upper", "extra", "missing"])
        uuids = [k for k, v in f.items() if k != "command" and M.valid_uuid(v) and any(c.isalpha() for c in v)]
        required = [k for k in f if k not in ("command", "meta", "in_reply_to_eml_url")]
        if how == "upper" and uuids:
            k = rng.choice(uuids)
            f[k] = f[k].upper()
        elif how == "missing" and required:
            del f[rng.choice(required)]
        else:
            f["extra"] = 1
        return f

    def live(self, sid):
        s = self.streams[sid]
        return s.opened and not s.closed

    # ---- the core ----

    @initialize(data=st.data())
    def maybe_open(self, data):
        """Most runs start with S open by ann and her cast declared and delegated; some open T too, some start cold."""
        if not data.draw(st.sampled_from([True] * 5 + [False])):
            return
        self.send(ANN, {"command": "stream.open", "proof_revision_url": PROOF_URL}, [S])
        cast = [(ANN, "principal.invite", "principal_id", CY), (ANN, "principal.summon", "principal_id", DEE),
                (ANN, "principal.summon", "principal_id", EVE), (ANN, "principal.invite", "principal_id", FAY),
                (ANN, "principal.delegate", "delegate_id", EVE), (ANN, "principal.delegate", "delegate_id", FAY),
                (EVE, "principal.invite", "principal_id", HAL), (EVE, "principal.summon", "principal_id", GUS),
                (HAL, "principal.delegate", "delegate_id", GUS)]
        upto = data.draw(st.sampled_from([len(cast)] * 4 + [3, 6]))
        for actor, cmd, field, p in cast[:upto]:
            self.send(actor, {"command": cmd, "stream_id": S, field: p})
        if data.draw(st.sampled_from([False] * 3 + [True])):
            self.send(BEN, {"command": "stream.open", "proof_revision_url": PROOF_URL}, [T])
            self.streams[T].opened_while_other_open = True
            self.send(BEN, {"command": "principal.summon", "stream_id": T, "principal_id": EVE})

    @rule(data=st.data())
    def open_stream(self, data):
        sid = data.draw(st.sampled_from([S, T]))
        other = self.streams[T if sid == S else S]
        fresh = data.draw(st.sampled_from([[sid]] * 6 + [[], [sid, U("extra")]]))
        got = self.send(data.draw(st.sampled_from(PRINCIPALS)),
                        self.with_meta(data, {"command": "stream.open", "proof_revision_url": PROOF_URL}), fresh)
        if got.get("accept") and other.opened and not other.closed:
            self.streams[sid].opened_while_other_open = True

    @precondition(lambda self: self.steps > 40)
    @rule(data=st.data())
    def close_stream(self, data):
        if data.draw(st.sampled_from([True] * 3 + [False])):
            return
        sid = data.draw(st.sampled_from([S, T]))
        s = self.streams[sid]
        actor = s.opener if s.opener and data.draw(st.booleans()) else data.draw(st.sampled_from(PRINCIPALS))
        self.send(actor, {"command": "stream.close", "stream_id": sid})

    # ---- the layer: a command, mostly one the model accepts ----

    def step_command(self, data, cmd, sid=None, valid_bias=4, item=None):
        rng = random.Random(data.draw(st.integers(0, 2 ** 32 - 1)))
        sid = sid or rng.choice([S] * 5 + [T, NEVER])
        s = self.streams[sid]
        cands = self.candidates(s, cmd)
        if item is not None:
            cands = [c for c in cands if item in (c[1].get("email_id"), c[1].get("triage_id"))]
        if not cands:
            return None
        ok = [c for c in cands if self.judge(s, c) is None]
        cand = rng.choice(ok) if ok and rng.randrange(valid_bias + 1) else rng.choice(cands)
        actor, f, fresh = cand
        if rng.randrange(30) == 0:
            f = self.mangle(rng, f)
        return self.send(actor, self.with_meta(data, f), fresh)

    @rule(data=st.data(), cmd=st.sampled_from([c for c in M.LAYER if c not in TERMINALS]))
    def a_command(self, data, cmd):
        self.step_command(data, cmd)

    @rule(data=st.data(), cmd=st.sampled_from([c for c in M.LAYER if c not in TERMINALS]))
    def another_command(self, data, cmd):
        self.step_command(data, cmd)

    @rule(data=st.data(), cmd=st.sampled_from(TERMINALS))
    def a_terminal(self, data, cmd):
        """Terminal decisions are held back, so that work accumulates on the items."""
        if data.draw(st.sampled_from([True] * 2 + [False])):
            return
        self.step_command(data, cmd)

    # ---- scenarios: a few valid steps on one item, so that the deep states are reached ----

    def valid(self, data, cmd, sid, item=None, actors=None):
        """Send a request for `cmd` the model accepts, by one of `actors` when given; False when there is none."""
        s = self.streams[sid]
        rng = random.Random(data.draw(st.integers(0, 2 ** 32 - 1)))
        cands = [c for c in self.candidates(s, cmd)
                 if (item is None or item in (c[1].get("email_id"), c[1].get("triage_id")))
                 and (actors is None or c[0] in actors) and self.judge(s, c) is None]
        if not cands:
            return False
        actor, f, fresh = rng.choice(cands)
        self.send(actor, f, fresh)
        return True

    def delegates(self, s, person=None):
        ds = s.delegates()
        if person is None:
            return ds
        return [d for d in ds if s.invited(d) == person]

    @rule(data=st.data())
    def scenario_email(self, data):
        """An email created (by a delegate, at times), solicited and prepared, drafted by an agent and by the owner,
        solicited and prepared again after the draft, and sent by a person delegate or the owner."""
        if not self.live(S):
            return
        s = self.streams[S]
        live = s.undecided_emails()
        k = data.draw(st.sampled_from(live)) if live and data.draw(st.booleans()) else None
        if k is None:
            new = [e for e in EMAILS if not s.noted("email", e)]
            if not new:
                return
            k = new[0]
            actors = self.delegates(s) if data.draw(st.booleans()) and self.delegates(s) else [s.opener]
            if not self.valid(data, "email.create", S, k, actors):
                return
        for cmd in ("email.solicit", "email.prepare"):
            self.valid(data, cmd, S, k)
        self.valid(data, "email.draft", S, k, self.delegates(s, person=False) or None)
        if data.draw(st.booleans()):
            self.valid(data, "email.draft", S, k, [s.opener])
        for cmd in ("email.solicit", "email.prepare"):
            self.valid(data, cmd, S, k)
        if data.draw(st.sampled_from([True, False, False])):
            self.valid(data, data.draw(st.sampled_from(["email.send", "email.discard"])), S, k,
                       self.delegates(s, person=True) or None)

    @rule(data=st.data())
    def scenario_triage(self, data):
        """A triage requested (by a delegate, at times), asked and advised, considered by an agent, asked and advised
        again after the consideration, and decided: a reply with an email made for it, or another terminal."""
        if not self.live(S):
            return
        s = self.streams[S]
        live = s.undecided_triages()
        k = data.draw(st.sampled_from(live)) if live and data.draw(st.booleans()) else None
        if k is None:
            new = [t for t in TRIAGES if not s.noted("triage", t)]
            if not new:
                return
            k = new[0]
            actors = self.delegates(s) if data.draw(st.booleans()) and self.delegates(s) else [s.opener]
            if not self.valid(data, "triage.request", S, k, actors):
                return
        for cmd in ("triage.ask", "triage.advise"):
            self.valid(data, cmd, S, k)
        self.valid(data, "triage.consider", S, k, self.delegates(s, person=False) or None)
        if data.draw(st.booleans()):
            self.valid(data, "triage.consider", S, k, [s.opener])
        for cmd in ("triage.ask", "triage.advise", "triage.advise"):
            self.valid(data, cmd, S, k)
        if data.draw(st.sampled_from([True, False])):
            how = data.draw(st.sampled_from(["triage.reply", "triage.reply", "triage.work", "triage.ignore",
                                             "triage.defer"]))
            deciders = self.delegates(s, person=True) or None
            if how == "triage.reply" and not s.unclaimed_emails():
                msg = [n[2] for n in s.notes if n[0] == "triage" and n[1] == k]
                new = [e for e in EMAILS if not s.noted("email", e)]
                if new and msg:
                    self.send(s.opener, {"command": "email.create", "stream_id": S, "email_id": new[0],
                                         "in_reply_to_eml_url": msg[0]})
            self.valid(data, how, S, k, deciders)

    def refused_for(self, data, cmd, sid, item, reason):
        """Send a request for `cmd` on `item` that the model refuses for `reason`, when there is one."""
        s = self.streams[sid]
        rng = random.Random(data.draw(st.integers(0, 2 ** 32 - 1)))
        cands = [c for c in self.candidates(s, cmd) if item in (c[1].get("email_id"), c[1].get("triage_id"))]
        rng.shuffle(cands)
        for c in cands:
            if self.judge(s, c) == reason:
                self.send(*c)
                return

    @rule(data=st.data())
    def scenario_decided_with_work_waiting(self, data):
        """An item is decided while a preparer or an adviser is still at work; the work that follows meets
        email_must_be_undecided or triage_must_be_undecided, which need exactly this state."""
        if data.draw(st.sampled_from([True] * 2 + [False])) or not self.live(S):
            return
        s = self.streams[S]
        if data.draw(st.booleans()):
            live = s.undecided_emails()
            if not live:
                return
            k = data.draw(st.sampled_from(live))
            self.valid(data, "email.solicit", S, k)
            if self.valid(data, data.draw(st.sampled_from(["email.send", "email.discard"])), S, k):
                for cmd in ("email.solicit", "email.prepare", "email.draft"):
                    self.refused_for(data, cmd, S, k, "email_must_be_undecided")
        else:
            live = s.undecided_triages()
            if not live:
                return
            k = data.draw(st.sampled_from(live))
            self.valid(data, "triage.ask", S, k)
            how = data.draw(st.sampled_from(["triage.work", "triage.ignore", "triage.defer"]))
            if self.valid(data, how, S, k):
                for cmd in ("triage.ask", "triage.advise", "triage.consider"):
                    self.refused_for(data, cmd, S, k, "triage_must_be_undecided")

    # ---- refusals, aimed: a request the model refuses for a drawn rule, found by search ----

    def aim(self, rng, cmd, reason):
        """`(actor, command, fresh)` the model refuses for `reason`, or None when this state offers none."""
        streams = [self.streams[x] for x in (S, T)]
        if reason == "malformed":
            s = self.streams[S]
            cands = self.candidates(s, cmd)
            if not cands:
                return None
            a, f, fresh = rng.choice(cands)
            return a, self.mangle(rng, f), fresh
        if reason == "fresh_ids_must_match_the_command":
            s = self.streams[S]
            a, f, fresh = rng.choice(self.candidates(s, cmd))
            return a, f, (rng.choice([[], [s.id, U("extra")]]) if cmd == "stream.open" else [U("extra")])
        if reason == "stream_must_exist":
            a, f, fresh = rng.choice(self.candidates(self.streams[NEVER], cmd))
            return a, f, fresh
        if reason == "stream_must_be_open" and not any(x.closed for x in streams):
            if self.live(T):
                self.send(self.streams[T].opener, {"command": "stream.close", "stream_id": T})
        pool = [x for x in streams if x.closed] if reason == "stream_must_be_open" else streams + [self.streams[NEVER]]
        for s in pool:
            cands = self.candidates(s, cmd)
            rng.shuffle(cands)
            for c in cands:
                if self.judge(s, c) == reason:
                    return c
        return None

    def aimed(self, data):
        """One aimed refusal. Targets the run has not yet observed come first, so that the run's coverage converges;
        then the targets in turn from a drawn start."""
        rng = random.Random(data.draw(st.integers(0, 2 ** 32 - 1)))
        unseen = [t for t in TARGETS if SEEN[t] == 0]
        rng.shuffle(unseen)
        start = rng.randrange(len(TARGETS)) + self.steps
        order = unseen[:12] + [TARGETS[(start + i * 7) % len(TARGETS)] for i in range(6)]
        for cmd, reason in order:
            built = self.aim(rng, cmd, reason)
            if built is not None:
                self.send(*built)
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

    @rule(data=st.data())
    def aimed_pair(self, data):
        """A request two rules of one command both refuse, so that the first in the engine's order must answer."""
        rng = random.Random(data.draw(st.integers(0, 2 ** 32 - 1)))
        if not self.live(S):
            return
        s = self.streams[S]
        start = rng.randrange(len(PAIR_TARGETS))
        for offset in range(4):
            cmd, a, b = PAIR_TARGETS[(start + offset * 11) % len(PAIR_TARGETS)]
            cands = self.candidates(s, cmd)
            rng.shuffle(cands)
            for c in cands:
                fails = M.failing_rules(s, c[0], cmd, c[1])
                if a in fails and b in fails:
                    self.send(*c)
                    EXTRA["rule pairs sent"] += 1
                    return

    # ---- the acceptance theorems, as rules ----

    def undecided(self, which):
        return [(s, k) for s in self.streams.values() if s.opened and not s.closed
                for k in (s.undecided_emails() if which == "email" else s.undecided_triages())]

    def deciders(self, s):
        return [s.opener] + [d for d in s.delegates() if s.invited(d)]

    @precondition(lambda self: bool(self.undecided("email")))
    @rule(data=st.data())
    def the_creator_can_always_send(self, data):
        if data.draw(st.sampled_from([True] * 3 + [False])):
            return
        s, k = data.draw(st.sampled_from(self.undecided("email")))
        a = data.draw(st.sampled_from(self.deciders(s)))
        got = self.send(a, {"command": "email.send", "stream_id": s.id, "email_id": k, "sent_eml_url": self.unnamed(s, k)})
        self.check(got.get("accept") is True, "the_creator_can_always_send", got)
        EXTRA["the_creator_can_always_send: as a rule"] += 1

    @precondition(lambda self: bool(self.undecided("triage")))
    @rule(data=st.data(), cmd=st.sampled_from(["triage.ignore", "triage.defer", "triage.reply"]))
    def the_creator_can_always_decide(self, data, cmd):
        if data.draw(st.sampled_from([True] * 3 + [False])):
            return
        s, k = data.draw(st.sampled_from(self.undecided("triage")))
        a = data.draw(st.sampled_from(self.deciders(s)))
        f = {"command": cmd, "stream_id": s.id, "triage_id": k}
        if cmd == "triage.reply":
            if not s.unclaimed_emails():
                new = [e for e in EMAILS if not s.noted("email", e)]
                if not new:
                    return
                self.send(s.opener, {"command": "email.create", "stream_id": s.id, "email_id": new[0]})
            f["email_id"] = s.unclaimed_emails()[0]
        got = self.send(a, f)
        name = {"triage.ignore": "the_creator_can_always_ignore", "triage.defer": "the_creator_can_always_defer",
                "triage.reply": "the_creator_can_always_reply"}[cmd]
        self.check(got.get("accept") is True, name, got)
        EXTRA["%s: as a rule" % name] += 1

    # ---- the acceptance theorems, at every step ----

    def probe(self, s, snap, actor, cmd, theorem):
        req = {"actor_id": actor, "fresh": [], "command": cmd}
        self.check(M.judge(s, req) is None, "the model must accept", theorem, req)
        got = self.engine.decide(req)
        RUNS["requests"] += 1
        self.trace.append({"request": req, "answer": got, "want": None, "probe": True})
        self.check(got.get("accept") is True and got["at"] == len(s.events), theorem, req, got)
        self.check(got["event"] == M.event_of(req, s.id), "the probe's event", theorem, got["event"])
        self.engine.load(s.id, snap["k"], snap["state"])
        EXTRA["%s: as a probe" % theorem] += 1

    @invariant()
    def the_creator_can_always_decide_everywhere(self):
        for s in self.streams.values():
            if not (s.opened and not s.closed):
                continue
            live_e, live_t = s.undecided_emails(), s.undecided_triages()
            if not live_e and not live_t:
                continue
            snap = self.engine.snapshot(s.id)
            self.check(snap["k"] == len(s.events), "the snapshot's length", snap["k"], len(s.events))
            for k in live_e:
                for a in self.deciders(s)[:2]:
                    self.probe(s, snap, a, {"command": "email.send", "stream_id": s.id, "email_id": k,
                                            "sent_eml_url": self.unnamed(s, k)}, "the_creator_can_always_send")
            unclaimed = s.unclaimed_emails()
            for k in live_t:
                base = {"stream_id": s.id, "triage_id": k}
                self.probe(s, snap, s.opener, dict(base, command="triage.ignore"), "the_creator_can_always_ignore")
                self.probe(s, snap, s.opener, dict(base, command="triage.defer"), "the_creator_can_always_defer")
                if unclaimed:
                    self.probe(s, snap, self.deciders(s)[-1], dict(base, command="triage.reply", email_id=unclaimed[0]),
                               "the_creator_can_always_reply")
            got = self.engine.query({"query": "stream", "stream_id": s.id})
            self.check(got == s.read(), "the read after the snapshot is loaded back", got, s.read())

    # ---- the theorems, as invariants of the accepted log ----

    @invariant()
    def theorems_hold(self):
        for s in self.streams.values():
            if not s.opened:
                self.check(not s.events, "events on a stream never opened")
                continue
            o = s.opener
            invited, summoned, delegator = set(), set(), {}
            emails, preparers, drafters, emls, e_decided = set(), {}, {}, {}, set()
            triages, advisers, advised, considerers, t_decided, claimed = set(), {}, {}, {}, set(), set()
            for e in s.events:
                name, a = e["event"], e["actor_id"]
                if name in ("stream.opened", "stream.closed"):
                    if name == "stream.closed":
                        self.check(a == o, "only_the_opener_closes_the_stream")
                        self.check(e is s.events[-1], "nothing_follows_a_close")
                    continue
                authority = a == o or delegator.get(a) == o
                if name in ("principal.invited", "principal.summoned"):
                    p = e["principal_id"]
                    self.check(authority, "every_declaration_is_by_the_opener_or_a_delegate")
                    self.check(p not in invited and p not in summoned, "a_principal_is_declared_once")
                    self.check(p != o, "the_opener_is_never_declared")
                    (invited if name == "principal.invited" else summoned).add(p)
                    continue
                if name == "principal.delegated":
                    d = e["delegate_id"]
                    self.check(a == o or a in invited, "every_delegator_is_a_person")
                    self.check(d in invited or d in summoned, "every_delegate_is_declared")
                    self.check(a != d, "no_principal_delegates_itself")
                    self.check(d not in delegator, "each_delegate_has_one_delegator")
                    delegator[d] = a
                    continue
                if name in ("email.sent", "email.discarded", "triage.replied", "triage.worked", "triage.ignored",
                            "triage.deferred"):
                    self.check(a == o or (delegator.get(a) == o and a in invited),
                               "every_terminal_decision_is_by_the_owner_or_a_person_delegate")
                    self.check(a not in summoned, "no_agent_makes_a_terminal_decision")
                elif name not in ("email.prepared", "triage.advised"):
                    self.check(authority, "every_act_is_by_the_owner_or_a_delegate")
                    if a != o:
                        self.check(delegator.get(a) == o, "no_act_rests_on_a_chain")
                if name.startswith("email."):
                    k = e["email_id"]
                    if name != "email.created":
                        self.check(k in emails, "every_event_names_a_created_email")
                    self.check(k not in e_decided, "Email.nothing_follows_a_decision")
                    field = {"email.created": "in_reply_to_eml_url", "email.drafted": "draft_eml_url",
                             "email.sent": "sent_eml_url"}.get(name)
                    if field and e.get(field) is not None:
                        self.check(e[field] not in emls.setdefault(k, set()), "emls_are_distinct")
                        emls[k].add(e[field])
                    if name == "email.created":
                        self.check(k not in emails, "an_email_is_created_once")
                        emails.add(k)
                    elif name == "email.solicited":
                        p = e["preparer_id"]
                        self.check(p != o, "no_preparer_is_the_owner")
                        self.check(p in invited or p in summoned, "every_solicited_preparer_was_declared")
                        self.check(p != a, "no_preparer_is_its_soliciter")
                        self.check(p not in preparers.setdefault(k, set()), "a_preparer_is_solicited_once")
                        self.check(p not in drafters.get(k, set()), "no_preparer_is_a_drafter")
                        preparers[k].add(p)
                    elif name == "email.prepared":
                        self.check(a in preparers.get(k, set()), "every_preparation_is_by_a_solicited_preparer")
                    elif name == "email.drafted":
                        self.check(a not in preparers.get(k, set()), "no_preparer_is_a_drafter")
                        drafters.setdefault(k, set()).add(a)
                    else:
                        self.check(k not in e_decided, "an_email_is_decided_once")
                        e_decided.add(k)
                else:
                    k = e["triage_id"]
                    if name != "triage.requested":
                        self.check(k in triages, "every_event_names_a_requested_triage")
                    self.check(k not in t_decided, "Triage.nothing_follows_a_decision")
                    if name == "triage.requested":
                        self.check(k not in triages, "a_triage_is_requested_once")
                        triages.add(k)
                    elif name == "triage.asked":
                        d = e["adviser_id"]
                        self.check(d != o, "no_adviser_is_the_owner")
                        self.check(d in invited or d in summoned, "every_asked_adviser_was_declared")
                        self.check(d != a, "no_adviser_is_its_asker")
                        self.check(d not in advisers.setdefault(k, set()), "an_adviser_is_asked_once")
                        self.check(d not in considerers.get(k, set()), "no_adviser_is_a_considerer")
                        advisers[k].add(d)
                    elif name == "triage.advised":
                        self.check(a in advisers.get(k, set()), "every_advice_is_by_an_asked_adviser")
                        self.check(a not in advised.setdefault(k, set()), "an_adviser_advises_once")
                        self.check(e["verdict"] in M.VERDICTS, "a verdict")
                        advised[k].add(a)
                    elif name == "triage.considered":
                        self.check(a not in advisers.get(k, set()), "no_adviser_is_a_considerer")
                        self.check(e["verdict"] in M.VERDICTS, "a verdict")
                        considerers.setdefault(k, set()).add(a)
                    else:
                        self.check(k not in t_decided, "a_triage_is_decided_once")
                        t_decided.add(k)
                        if name == "triage.replied":
                            x = e["email_id"]
                            self.check(x in emails, "every_reply_names_a_created_email")
                            self.check(x not in claimed, "an_email_answers_one_triage")
                            claimed.add(x)

    @invariant()
    def read_is_the_notes(self):
        for s in self.streams.values():
            got = self.engine.query({"query": "stream", "stream_id": s.id})
            self.check(got == s.read(), "the read is the notes", got, s.read())


EXAMPLES = int(os.environ.get("MAILBOX_EXAMPLES", "300"))
STEPS = int(os.environ.get("MAILBOX_STEPS", "60"))
TestMailbox = MailboxMachine.TestCase
TestMailbox.settings = settings(max_examples=EXAMPLES, stateful_step_count=STEPS, deadline=None, database=None,
                                suppress_health_check=[HealthCheck.too_slow])


def _ran():
    if RUNS["runs"] == 0:
        pytest.skip("the state machine did not run in this session")


def test_coverage_is_complete():
    """Derived from the engine's own description: every (command, rule) the description lists was the reason of some
    refusal; every command was accepted and refused as malformed at least once; a wrong number of fresh ids was refused
    on an open and on each create; each acceptance theorem fired as a rule and as a probe."""
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
    for c in ("stream.open", "email.create", "triage.request"):
        expected.add((c, "fresh_ids_must_match_the_command"))
    missing = sorted(p for p in expected if SEEN[p] == 0)
    assert not missing, "never observed in %d runs: %s" % (RUNS["runs"], missing)
    unexpected = sorted(p for p in SEEN if p not in expected and p[1] != "accepted")
    assert not unexpected, "observed but not described: %s" % unexpected
    for theorem in ACCEPTANCE:
        assert EXTRA["%s: as a rule" % theorem] > 0, "%s never fired as a rule" % theorem
        assert EXTRA["%s: as a probe" % theorem] > 0, "%s was never probed" % theorem


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
    reply = next(c for c in described if c["name"] == "triage.reply")
    assert reply["rules"][-1] == "reply_must_name_an_unclaimed_email"


def test_deep_states_are_reached():
    _ran()
    missing = [name for name in DEEP_STATES if DEEP[name] == 0]
    assert not missing, "deep states never reached in %d runs: %s" % (RUNS["runs"], missing)
