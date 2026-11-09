#!/usr/bin/env python3
# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Write the conformance cases (`cases/*.jsonl`), deterministically: one file per theme, one case per line, run in
order as one session per file (`provenstream conform`, host/provenstream/conform.py, reads them; README.md says what
the patterns mean). The answer table's codes and messages, every proof's description and every proof's rules are
written out here, not imported from the host or the engines, so the cases are a statement about a host and the proofs
it serves rather than a copy of either.

Two kinds of theme:

- one per proof (`core`, `log`, `principals`, `tasks`, `work`, `tower`): many command sequences, each opening a stream of its
  own and sending it commands, valid and invalid, by several principals. Every answer is what a model of the proof's
  rules here (`Model`) says, independently of the Lean: accepted with its exact event at its seq, refused with the rule
  that refuses it (the first that fails, in the proof's order), method_not_found, or invalid_params. Each sequence ends
  by reading its stream back: every event with its seq and the chain head its command's answer gave, the head, the
  engine's view as the model has it, and the stored rows, whose hash chain the runner recomputes. Some sequences are
  written by hand, one or more per rule; the rest are drawn from a seeded generator, so they are the same on every
  run.
- the host's own (`auth`, `parse`, `reads`, `paging`, `idempotency`, `discovery`, `host`, `actor`, `errors`).

    python3 conformance/make_cases.py           write every file
    python3 conformance/make_cases.py --check   write nothing; fail if a file differs from what this script writes
"""
import base64, json, os, random, sys

HERE = os.path.dirname(os.path.abspath(__file__))
CASES = os.path.join(HERE, "cases")

# The answer table of protocol 2: code -> (JSON-RPC code, message).
TABLE = {
    "parse_error": (-32700, "parse error"),
    "invalid_request": (-32600, "invalid request"),
    "method_not_found": (-32601, "method not found"),
    "invalid_params": (-32602, "invalid params"),
    "unauthorized": (-32001, "unauthorized"),
    "refused": (-32002, "refused"),
    "unavailable": (-32003, "unavailable"),
}
PROTOCOL = 2

NOWHERE = "00000000-0000-4000-8000-000000000000"          # a stream no host has: never opened
UNISSUED = "00000000-0000-4000-8000-000000000001"         # a principal no host issued (the proofs cannot tell)
UPPER_COMMIT = "4F1C2A9E0B7D3C6A5F8E1D2C3B4A59687F6E5D4C"     # no revision: uppercase
NO_COMMIT = "0" * 40                                      # a commit no host serves
DETAIL = "$string"                                        # a detail is prose for people: its words are not the contract
ROLES = ("opener", "other", "third", "outsider")          # the principals of a run (README.md)
PROOFS = ("core", "log", "principals", "tasks", "work", "tower")
PACKAGES = {"core": "", "log": "examples/log", "principals": "examples/principals", "tasks": "examples/tasks",
            "work": "examples/work", "tower": "tests/tower"}
TASK = ["70000000-0000-4000-8000-0000000000%02d" % i for i in range(1, 10)]   # task ids (any UUIDs)
WORK = ["80000000-0000-4000-8000-0000000000%02d" % i for i in range(1, 10)]   # work item ids (any UUIDs)

# -- the proofs' descriptions, as their engines give them ------------------------------------------------------------

EV = ["event", "stream_id", "actor_id", "meta"]
ADMISSION = ["stream_must_exist", "stream_must_be_open"]


def command(name, event, params, rules, who, extra=(), minted=()):
    return {"name": name, "params": [{"name": n, "kind": k} for n, k in params], "minted": list(minted),
            "fresh": len(minted), "stream_id": "stream_id", "who": who,
            "event": {"name": event, "fields": EV + list(extra)}, "rules": rules}


OPENER = "the stream's opener"
ADMIN = "an admin: the stream's opener, or a principal promoted in the stream"
OPEN = command("stream.open", "stream.opened", [("proof_revision_url", "text"), ("meta", "meta")],
               ["stream_id_must_be_new", "revision_url_must_name_a_commit"],
               "anyone signed in; the caller becomes the stream's opener", ["proof_revision_url"], ["stream_id"])
CLOSE_PARAMS = [("stream_id", "uuid"), ("meta", "meta")]
CLOSE = command("stream.close", "stream.closed", CLOSE_PARAMS, ADMISSION + ["only_opener_can_close"], OPENER)
TASK_COMMANDS = [
    command("task.open", "task.opened", [("stream_id", "uuid"), ("task_id", "uuid"), ("parent_task_id", "uuid?"),
                                         ("meta", "meta")],
            ADMISSION + ["only_opener_can_open_tasks", "task_id_must_be_new", "parent_task_must_exist"], OPENER,
            ["task_id", "parent_task_id"]),
    command("task.assign", "task.assigned", [("stream_id", "uuid"), ("task_id", "uuid"), ("assignee_id", "uuid"),
                                             ("meta", "meta")],
            ADMISSION + ["only_opener_can_assign", "task_must_exist", "task_is_assigned_once"], OPENER,
            ["task_id", "assignee_id"]),
    command("task.complete", "task.completed", [("stream_id", "uuid"), ("task_id", "uuid"), ("meta", "meta")],
            ADMISSION + ["task_must_exist", "only_assignee_can_finish", "task_is_completed_once"],
            "the task's assignee", ["task_id"]),
]
ASSIGNEE = "the item's assignee"
WORK_PARAMS = [("stream_id", "uuid"), ("work_id", "uuid"), ("meta", "meta")]
WORK_COMMANDS = [
    command("work.create", "work.created", WORK_PARAMS, ADMISSION + ["only_opener_can_create", "work_id_must_be_new"],
            OPENER, ["work_id"]),
    command("work.assign", "work.assigned", [("stream_id", "uuid"), ("work_id", "uuid"), ("assignee_id", "uuid"),
                                             ("meta", "meta")],
            ADMISSION + ["only_opener_can_assign", "work_must_exist", "work_is_assigned_once"], OPENER,
            ["work_id", "assignee_id"]),
    command("work.ask", "work.asked", [("stream_id", "uuid"), ("work_id", "uuid"), ("preparer_id", "uuid"),
                                       ("meta", "meta")],
            ADMISSION + ["work_must_exist", "only_assignee_can_ask", "work_must_be_undecided",
                         "preparer_must_not_be_the_assignee", "preparer_is_asked_once"], ASSIGNEE,
            ["work_id", "preparer_id"]),
    command("work.reply", "work.replied", WORK_PARAMS,
            ADMISSION + ["work_must_exist", "only_asked_preparers_can_reply", "work_must_be_undecided"],
            "a preparer the assignee asked", ["work_id"]),
    command("work.complete", "work.completed", WORK_PARAMS,
            ADMISSION + ["work_must_exist", "only_assignee_can_decide", "work_is_decided_once"], ASSIGNEE, ["work_id"]),
    command("work.cancel", "work.cancelled", WORK_PARAMS,
            ADMISSION + ["work_must_exist", "only_assignee_can_decide", "work_is_decided_once"], ASSIGNEE, ["work_id"]),
]
PRINCIPAL_PARAMS = [("stream_id", "uuid"), ("principal_id", "uuid"), ("meta", "meta")]
DESCRIPTIONS = {
    "core": [OPEN, CLOSE],
    "log": [OPEN, CLOSE, command("log.append", "log.appended", [("stream_id", "uuid"), ("text", "text"),
                                                                ("meta", "meta")],
                                 ADMISSION + ["only_opener_can_append"], OPENER, ["text"])],
    "principals": [OPEN, CLOSE] + [
        command("principal." + verb, "principal." + past, PRINCIPAL_PARAMS, ADMISSION + rules, ADMIN, ["principal_id"])
        for verb, past, rules in (
            ("invite", "invited", ["only_admins_can_invite", "principal_must_be_new"]),
            ("promote", "promoted", ["only_admins_can_promote", "principal_must_be_invited",
                                     "principal_is_promoted_once"]),
            ("summon", "summoned", ["only_admins_can_summon", "principal_must_be_new"]))],
    "tasks": [OPEN, CLOSE] + TASK_COMMANDS,
    "work": [OPEN, CLOSE] + WORK_COMMANDS,
    "tower": [OPEN, command("stream.close", "stream.closed", CLOSE_PARAMS,
                            ADMISSION + ["only_opener_can_close", "completed_tasks_must_be_approved_before_close"],
                            OPENER)] + TASK_COMMANDS + [
        command("review.approve", "review.approved", [("stream_id", "uuid"), ("task_id", "uuid"), ("meta", "meta")],
                ADMISSION + ["only_opener_can_approve", "task_must_be_completed", "task_is_approved_once"], OPENER,
                ["task_id"])],
}
COMMANDS = {p: [c["name"] for c in d] for p, d in DESCRIPTIONS.items()}
SPEC = {p: {c["name"]: c for c in d} for p, d in DESCRIPTIONS.items()}


def described(proof):
    return {"revision": "$commit", "repo": "$string", "package": PACKAGES[proof], "protocol": PROTOCOL,
            "schema": {"commands": DESCRIPTIONS[proof]}}


# -- answers ----------------------------------------------------------------------------------------------------------

def ok(result):
    return {"result": result}


def err(code, **data):
    rpc, message = TABLE[code]
    return {"error": {"code": rpc, "message": message, "data": dict({"code": code}, **data)}}


def refused(reason):
    return err("refused", reason=reason)


def bad_params():
    return err("invalid_params", detail=DETAIL)


NOT_FOUND = err("method_not_found", detail=DETAIL)
UNAUTHORIZED = err("unauthorized")


def accepted(seq, event, chain):
    return ok({"seq": seq, "event": event, "chain": chain})


def call(name, who, method, params=None, expect=None, **extra):
    c = {"id": name, "who": who, "method": method}
    if params is not None:
        c["params"] = params
    c.update(extra)
    c["expect"] = expect
    return c


def raw(name, text, expect, answer_id=None, who="opener", **extra):
    """A message given as its bytes: `text` (UTF-8), or with `raw_base64` any bytes, or with `oversize` a request over
    1 MiB that the runner builds."""
    c = {"id": name, "who": who}
    if text is not None:
        c["raw"] = text
    c.update(extra)
    c["answer_id"] = answer_id
    c["expect"] = expect
    return c


# -- the model of the proofs' rules ------------------------------------------------------------------------------------

class Model:
    """One stream of one proof, as its rules say it goes: the events so far (as patterns), the opener, whether it is
    closed, and what each layer remembers. `step` answers what a command gets, and records an accepted one."""

    def __init__(self, proof, name):
        self.proof, self.name = proof, name
        self.s = "$" + name
        self.events = []                          # (event pattern, chain binding)
        self.opener = None
        self.closed = False
        self.tasks, self.completed, self.assigned, self.approved = [], [], [], []
        self.invited, self.promoted, self.summoned = [], [], []
        self.work, self.work_assigned, self.asked, self.replied, self.work_completed, self.cancelled = \
            [], [], [], [], [], []

    # the view an engine of the proof answers stream.get with
    def view(self):
        v = {"stream_id": self.s, "proof_revision_url": "$url_" + self.proof, "opener_id": self.opener,
             "closed": self.closed}
        if self.proof == "principals":
            v.update(invited=list(self.invited), promoted=list(self.promoted), summoned=list(self.summoned))
        if self.proof in ("tasks", "tower"):
            v.update(tasks=list(self.tasks), completed=list(self.completed),
                     assigned=[{"task_id": t, "assignee_id": a} for t, a in self.assigned])
        if self.proof == "tower":
            v["approved"] = list(self.approved)
        if self.proof == "work":
            pairs = lambda xs, who: [{"work_id": k, who: q} for k, q in xs]
            v.update(work=list(self.work), assigned=pairs(self.work_assigned, "assignee_id"),
                     asked=pairs(self.asked, "preparer_id"), replied=pairs(self.replied, "preparer_id"),
                     completed=list(self.work_completed), cancelled=list(self.cancelled))
        return v

    def admins(self):
        return [self.opener] + self.promoted

    def assignee(self, task):
        return next((a for t, a in self.assigned if t == task), None)

    def work_assignee(self, k):
        return next((a for w, a in self.work_assigned if w == k), None)

    def decided(self, k):
        return k in self.work_completed or k in self.cancelled

    def rule(self, actor, cmd, p):
        """The first rule that refuses (None: accepted). The core's admission comes first, then a layer's rules; a
        layer's guard on a core command after the core's rules."""
        if self.opener is None:
            return "stream_must_exist"
        if self.closed:
            return "stream_must_be_open"
        if cmd == "stream.close":
            if actor != self.opener:
                return "only_opener_can_close"
            if self.proof == "tower" and any(t not in self.approved for t in self.completed):
                return "completed_tasks_must_be_approved_before_close"
            return None
        t = p.get("task_id")
        if cmd == "log.append":
            return None if actor == self.opener else "only_opener_can_append"
        if cmd in ("principal.invite", "principal.promote", "principal.summon"):
            verb, who = cmd.split(".")[1], p["principal_id"]
            if actor not in self.admins():
                return "only_admins_can_" + verb
            if verb == "promote":
                if who not in self.invited:
                    return "principal_must_be_invited"
                return "principal_is_promoted_once" if who in self.promoted else None
            new = who not in self.invited and who not in self.summoned and who != self.opener
            return None if new else "principal_must_be_new"
        if cmd == "task.open":
            parent = p.get("parent_task_id")
            if actor != self.opener:
                return "only_opener_can_open_tasks"
            if t in self.tasks:
                return "task_id_must_be_new"
            if parent is not None and parent not in self.tasks:
                return "parent_task_must_exist"
            return None
        if cmd == "task.assign":
            if actor != self.opener:
                return "only_opener_can_assign"
            if t not in self.tasks:
                return "task_must_exist"
            return "task_is_assigned_once" if self.assignee(t) is not None else None
        if cmd == "task.complete":
            if t not in self.tasks:
                return "task_must_exist"
            if self.assignee(t) != actor:
                return "only_assignee_can_finish"
            return "task_is_completed_once" if t in self.completed else None
        if cmd == "review.approve":
            if actor != self.opener:
                return "only_opener_can_approve"
            if t not in self.completed:
                return "task_must_be_completed"
            return "task_is_approved_once" if t in self.approved else None
        k = p.get("work_id")
        if cmd == "work.create":
            if actor != self.opener:
                return "only_opener_can_create"
            return "work_id_must_be_new" if k in self.work else None
        if cmd == "work.assign":
            if actor != self.opener:
                return "only_opener_can_assign"
            if k not in self.work:
                return "work_must_exist"
            return "work_is_assigned_once" if self.work_assignee(k) is not None else None
        if cmd == "work.ask":
            if k not in self.work:
                return "work_must_exist"
            if self.work_assignee(k) != actor:
                return "only_assignee_can_ask"
            if self.decided(k):
                return "work_must_be_undecided"
            if p["preparer_id"] == actor:
                return "preparer_must_not_be_the_assignee"
            return "preparer_is_asked_once" if (k, p["preparer_id"]) in self.asked else None
        if cmd == "work.reply":
            if k not in self.work:
                return "work_must_exist"
            if (k, actor) not in self.asked:
                return "only_asked_preparers_can_reply"
            if self.decided(k):
                return "work_must_be_undecided"
            return None                                  # a later reply supersedes the preparer's earlier one
        if cmd in ("work.complete", "work.cancel"):
            if k not in self.work:
                return "work_must_exist"
            if self.work_assignee(k) != actor:
                return "only_assignee_can_decide"
            return "work_is_decided_once" if self.decided(k) else None
        raise AssertionError(cmd)

    def event(self, actor, cmd, p):
        spec = SPEC[self.proof][cmd]
        e = {"event": spec["event"]["name"], "stream_id": self.s, "actor_id": actor, "meta": p.get("meta")}
        for f in spec["event"]["fields"][len(EV):]:
            e[f] = p.get(f)
        return e

    def apply(self, actor, cmd, p):
        t = p.get("task_id")
        if cmd == "stream.close":
            self.closed = True
        elif cmd == "task.open":
            self.tasks.append(t)
        elif cmd == "task.assign":
            self.assigned.append((t, p["assignee_id"]))
        elif cmd == "task.complete":
            self.completed.append(t)
        elif cmd == "review.approve":
            self.approved.append(t)
        elif cmd.startswith("principal."):
            {"invite": self.invited, "promote": self.promoted, "summon": self.summoned}[cmd.split(".")[1]].append(
                p["principal_id"])
        elif cmd == "work.create":
            self.work.append(p["work_id"])
        elif cmd == "work.assign":
            self.work_assigned.append((p["work_id"], p["assignee_id"]))
        elif cmd == "work.ask":
            self.asked.append((p["work_id"], p["preparer_id"]))
        elif cmd == "work.reply":
            self.replied.append((p["work_id"], actor))
        elif cmd == "work.complete":
            self.work_completed.append(p["work_id"])
        elif cmd == "work.cancel":
            self.cancelled.append(p["work_id"])

    def chain(self, seq):
        return "%s_c%d" % (self.name, seq)


class Sequence:
    """A sequence of cases on one new stream of `proof`: opened by `who`, then `step`s, then `reads`."""

    def __init__(self, proof, name, title, who="opener", meta=None):
        self.m = Model(proof, name.replace("-", "_"))
        self.proof, self.name, self.title = proof, name, title
        self.cases = []
        self.n = 0
        params = {"proof_revision_url": "$url_" + proof}
        if meta is not None:
            params["meta"] = meta
        actor = "$" + who
        ev = {"event": "stream.opened", "stream_id": "$uuid:" + self.m.name, "actor_id": actor, "meta": meta,
              "proof_revision_url": "$url_" + proof}
        self.add(who, "stream.open", params, accepted(0, ev, "$hex64:" + self.m.chain(0)), "open")
        self.m.opener = actor
        self.m.events.append((dict(ev, stream_id=self.m.s), self.m.chain(0)))

    def add(self, who, method, params, expect, label=None):
        self.n += 1
        cid = "%s/%02d-%s" % (self.name, self.n, label or method)
        self.cases.append(call(cid, who, method, params, expect, proof=self.proof))

    def step(self, who, cmd, label=None, actor_id=None, **params):
        """`cmd` by `who` with `params` (the stream is added): the model's answer."""
        p = dict({"stream_id": self.m.s}, **params)
        if actor_id is not None:
            p["actor_id"] = actor_id
        actor = "$" + who
        if actor_id is not None and actor_id != actor:
            self.add(who, cmd, p, refused("actor_id_must_match_the_token"), label)
            return
        if cmd not in SPEC[self.proof]:
            self.add(who, cmd, p, NOT_FOUND, label)
            return
        why = self.m.rule(actor, cmd, p)
        if why is not None:
            self.add(who, cmd, p, refused(why), label)
            return
        seq = len(self.m.events)
        ev = self.m.event(actor, cmd, p)
        self.add(who, cmd, p, accepted(seq, ev, "$hex64:" + self.m.chain(seq)), label)
        self.m.apply(actor, cmd, p)
        self.m.events.append((ev, self.m.chain(seq)))

    def invalid(self, who, cmd, label, **params):
        """A command whose params the engine (or the host) does not read: invalid_params, nothing stored."""
        self.add(who, cmd, dict({"stream_id": self.m.s}, **params), bad_params(), label)

    def reads(self, who="outsider"):
        """The stream read back, by anyone: its events with their seqs and receipts, its head, its view, its rows (whose
        chain the runner recomputes)."""
        evs = [dict(e, seq=i, chain="$" + c) for i, (e, c) in enumerate(self.m.events)]
        s = self.m.s
        last = "$" + self.m.events[-1][1]
        self.add(who, "stream.events", {"stream_id": s}, ok({"stream_id": s, "events": evs, "next": None}), "events")
        self.add(who, "stream.head", {"stream_id": s},
                 ok({"stream_id": s, "length": len(self.m.events), "chain": last}), "head")
        self.add(who, "stream.get", {"stream_id": s}, ok(self.m.view()), "view")
        rows = [{"seq": i, "request": "$any", "event": "$any", "meta_salt": "$any", "chain": "$" + c}
                for i, (_, c) in enumerate(self.m.events)]
        self.cases.append(dict(call("%s/%02d-rows" % (self.name, self.n + 1), who, "stream.rows", {"stream_id": s},
                                    ok({"stream_id": s, "rows": rows, "next": None}), proof=self.proof),
                               check="chain"))
        self.n += 1
        return self


# -- hand-written sequences, one or more per rule ----------------------------------------------------------------------

def core_sequences():
    out = []
    q = Sequence("core", "close", "only the opener closes; nothing follows a close", meta="a core stream")
    q.step("other", "stream.close", "close-by-other")
    q.step("outsider", "stream.close", "close-by-outsider")
    q.step("opener", "stream.close", "close-by-opener", meta="done")
    q.step("opener", "stream.close", "close-again")
    q.step("other", "stream.close", "close-by-other-after")
    out.append(q.reads())
    q = Sequence("core", "opened-by-other", "the opener is whoever opened it", who="other")
    q.step("opener", "stream.close", "close-by-the-first-role")
    q.step("other", "stream.close", "close-by-its-opener")
    out.append(q.reads("third"))
    q = Sequence("core", "foreign", "commands of other proofs are not this stream's")
    for cmd, params in (("log.append", {"text": "x"}), ("task.open", {"task_id": TASK[0]}),
                        ("principal.invite", {"principal_id": "$other"}), ("review.approve", {"task_id": TASK[0]}),
                        ("stream.panic", {})):
        q.step("opener", cmd, "foreign-" + cmd.replace(".", "-"), **params)
    q.invalid("opener", "stream.close", "meta-not-text", meta=5)
    q.invalid("opener", "stream.close", "meta-control", meta="a\u0001b")
    q.invalid("opener", "stream.close", "meta-too-long", meta="x" * 4097)
    q.invalid("opener", "stream.close", "unknown-param", x=1)
    q.invalid("opener", "stream.close", "fresh-id-sent", proof_revision_url="$url_core")
    q.step("opener", "stream.close", "meta-longest", meta="y" * 4096)
    out.append(q.reads())
    q = Sequence("core", "empty-meta", "meta may be empty")
    q.step("opener", "stream.close", "close-empty-meta", meta="")
    out.append(q.reads())
    return out


def log_sequences():
    out = []
    q = Sequence("log", "append", "only the opener appends")
    q.step("opener", "log.append", "append", text="the first line")
    q.step("other", "log.append", "append-by-other", text="not mine")
    q.step("outsider", "log.append", "append-by-outsider", text="nor mine")
    q.step("opener", "log.append", "append-empty", text="")
    q.step("opener", "log.append", "append-with-meta", text="two\nlines and é", meta="noted")
    q.step("opener", "log.append", "append-control", text="tab\tand \u0001")
    q.step("other", "stream.close", "close-by-other")
    q.step("opener", "stream.close", "close")
    q.step("opener", "log.append", "append-after-close", text="late")
    out.append(q.reads())
    q = Sequence("log", "malformed", "what the engine does not read", who="third")
    q.invalid("third", "log.append", "text-missing")
    q.invalid("third", "log.append", "text-not-a-string", text=5)
    q.invalid("third", "log.append", "text-nul", text="a\u0000b")
    q.invalid("third", "log.append", "unknown-param", text="x", y=1)
    q.invalid("third", "log.append", "meta-not-text", text="x", meta=[])
    q.step("third", "task.open", "foreign", task_id=TASK[0])
    q.step("third", "log.append", "append", text="after the malformed ones")
    q.step("opener", "log.append", "append-by-the-first-role", text="no")
    out.append(q.reads())
    return out


def principals_sequences():
    out = []
    q = Sequence("principals", "roles", "admins invite, promote and summon; agents never")
    q.step("opener", "principal.invite", "invite-other", principal_id="$other")
    q.step("other", "principal.summon", "summon-by-invitee", principal_id="$third")
    q.step("opener", "principal.promote", "promote-other", principal_id="$other")
    q.step("other", "principal.summon", "summon-by-promoted", principal_id="$third", meta="an agent")
    q.step("third", "principal.invite", "invite-by-agent", principal_id="$outsider")
    q.step("third", "principal.promote", "promote-by-agent", principal_id="$other")
    q.step("opener", "principal.promote", "promote-agent", principal_id="$third")
    q.step("opener", "principal.invite", "invite-opener", principal_id="$opener")
    q.step("opener", "principal.summon", "summon-opener", principal_id="$opener")
    q.step("opener", "principal.invite", "invite-again", principal_id="$other")
    q.step("opener", "principal.summon", "summon-invited", principal_id="$other")
    q.step("opener", "principal.invite", "invite-summoned", principal_id="$third")
    q.step("opener", "principal.promote", "promote-again", principal_id="$other")
    q.step("opener", "principal.promote", "promote-uninvited", principal_id="$outsider")
    q.step("outsider", "principal.summon", "summon-by-outsider", principal_id=UNISSUED)
    q.step("other", "principal.invite", "invite-by-promoted", principal_id="$outsider")
    q.step("other", "principal.promote", "promote-by-promoted", principal_id="$outsider")
    q.step("outsider", "principal.summon", "summon-by-new-admin", principal_id=UNISSUED)
    q.step("other", "stream.close", "close-by-admin")
    q.step("opener", "stream.close", "close")
    q.step("opener", "principal.invite", "invite-after-close", principal_id=UNISSUED)
    out.append(q.reads())
    q = Sequence("principals", "malformed", "principal ids are UUIDs, any of them")
    q.invalid("opener", "principal.invite", "principal-missing")
    q.invalid("opener", "principal.invite", "principal-not-an-id", principal_id="ann")
    q.invalid("opener", "principal.summon", "principal-uppercase", principal_id=UNISSUED.upper().replace("0", "A"))
    q.step("opener", "principal.invite", "invite-unissued", principal_id=UNISSUED)
    q.step("opener", "principal.promote", "promote-unissued", principal_id=UNISSUED)
    q.step("opener", "log.append", "foreign", text="x")
    out.append(q.reads())
    return out


def task_story(q, approve=False):
    """The tasks layer's rules, each once, on `q`."""
    q.step("opener", "task.open", "open-t1", task_id=TASK[0], meta="the first task")
    q.step("opener", "task.open", "open-t1-again", task_id=TASK[0])
    q.step("other", "task.open", "open-by-other", task_id=TASK[1])
    q.step("opener", "task.open", "open-child", task_id=TASK[1], parent_task_id=TASK[0])
    q.step("opener", "task.open", "parent-the-stream", task_id=TASK[2], parent_task_id=q.m.s)
    q.step("opener", "task.open", "parent-unknown", task_id=TASK[2], parent_task_id=TASK[8])
    q.step("opener", "task.open", "parent-itself", task_id=TASK[2], parent_task_id=TASK[2])
    q.step("other", "task.open", "parent-unknown-by-other", task_id=TASK[2], parent_task_id=TASK[8])
    q.step("opener", "task.open", "open-again-with-parent", task_id=TASK[0], parent_task_id=TASK[8])
    q.step("opener", "task.open", "open-t3-null-parent", task_id=TASK[2], parent_task_id=None)
    q.step("opener", "task.assign", "assign-t1", task_id=TASK[0], assignee_id="$other")
    q.step("other", "task.assign", "assign-by-other", task_id=TASK[1], assignee_id="$other")
    q.step("opener", "task.assign", "assign-unknown", task_id=TASK[8], assignee_id="$other")
    q.step("opener", "task.assign", "assign-again", task_id=TASK[0], assignee_id="$third")
    q.step("third", "task.complete", "complete-by-non-assignee", task_id=TASK[0])
    q.step("opener", "task.complete", "complete-by-opener", task_id=TASK[0])
    q.step("opener", "task.complete", "complete-unassigned", task_id=TASK[1])
    q.step("other", "task.complete", "complete-unknown", task_id=TASK[8])
    if approve:
        q.step("opener", "review.approve", "approve-uncompleted", task_id=TASK[0])
    q.step("other", "task.complete", "complete-t1", task_id=TASK[0])
    q.step("other", "task.complete", "complete-again", task_id=TASK[0])
    q.step("opener", "task.assign", "assign-to-self", task_id=TASK[1], assignee_id="$opener")
    q.step("opener", "task.complete", "complete-own", task_id=TASK[1], meta="mine")


def task_malformed(q):
    q.invalid("opener", "task.open", "task-not-an-id", task_id="t1")
    q.invalid("opener", "task.open", "task-missing")
    q.invalid("opener", "task.open", "parent-a-seq", task_id=TASK[5], parent_task_id=1)
    q.invalid("opener", "task.open", "parent-not-an-id", task_id=TASK[5], parent_task_id="t1")
    q.invalid("opener", "task.open", "parent-uppercase", task_id=TASK[5], parent_task_id="A" + TASK[0][1:])
    q.invalid("opener", "task.open", "parent-boolean", task_id=TASK[5], parent_task_id=True)
    q.invalid("opener", "task.open", "parent-list", task_id=TASK[5], parent_task_id=[TASK[0]])
    q.invalid("opener", "task.assign", "assignee-missing", task_id=TASK[0])
    q.invalid("opener", "task.complete", "unknown-param", task_id=TASK[0], assignee_id="$other")


def tasks_sequences():
    out = []
    q = Sequence("tasks", "story", "the opener opens and assigns; the assignee completes")
    task_story(q)
    q.step("opener", "review.approve", "foreign", task_id=TASK[0])
    q.step("other", "stream.close", "close-by-assignee")
    q.step("opener", "stream.close", "close-with-work-done")
    q.step("opener", "task.open", "open-after-close", task_id=TASK[4])
    out.append(q.reads())
    q = Sequence("tasks", "malformed", "what the engine does not read")
    task_malformed(q)
    q.step("opener", "task.open", "parent-of-another-stream", task_id=TASK[5], parent_task_id=TASK[0])
    q.step("opener", "task.open", "open", task_id=TASK[5])
    q.step("opener", "task.open", "child", task_id=TASK[6], parent_task_id=TASK[5])
    q.step("opener", "task.open", "grandchild", task_id=TASK[7], parent_task_id=TASK[6])
    q.step("opener", "task.assign", "assign-to-unissued", task_id=TASK[7], assignee_id=UNISSUED)
    q.step("other", "task.complete", "complete-by-other", task_id=TASK[7])
    out.append(q.reads())
    return out


def work_sequences():
    out = []
    q = Sequence("work", "story", "the opener creates and assigns; the assignee asks, the asked reply, the assignee "
                                  "decides")
    q.step("other", "work.create", "create-by-other", work_id=WORK[0])
    q.step("opener", "work.create", "create-w1", work_id=WORK[0], meta="the first item")
    q.step("opener", "work.create", "create-again", work_id=WORK[0])
    q.step("other", "work.assign", "assign-by-other", work_id=WORK[0], assignee_id="$other")
    q.step("opener", "work.assign", "assign-unknown", work_id=WORK[8], assignee_id="$other")
    q.step("other", "work.ask", "ask-unassigned", work_id=WORK[0], preparer_id="$third")
    q.step("other", "work.complete", "complete-unassigned", work_id=WORK[0])
    q.step("opener", "work.assign", "assign-w1", work_id=WORK[0], assignee_id="$other")
    q.step("opener", "work.assign", "assign-again", work_id=WORK[0], assignee_id="$third")
    q.step("opener", "work.ask", "ask-by-opener", work_id=WORK[0], preparer_id="$third")
    q.step("other", "work.ask", "ask-unknown", work_id=WORK[8], preparer_id="$third")
    q.step("other", "work.ask", "ask-itself", work_id=WORK[0], preparer_id="$other")
    q.step("third", "work.reply", "reply-unasked", work_id=WORK[0])
    q.step("other", "work.ask", "ask-third", work_id=WORK[0], preparer_id="$third", meta="please prepare")
    q.step("other", "work.ask", "ask-third-again", work_id=WORK[0], preparer_id="$third")
    q.step("other", "work.ask", "ask-outsider", work_id=WORK[0], preparer_id="$outsider")
    q.step("other", "work.ask", "ask-opener", work_id=WORK[0], preparer_id="$opener")
    q.step("third", "work.reply", "reply-unknown", work_id=WORK[8])
    q.step("other", "work.reply", "reply-by-assignee", work_id=WORK[0])
    q.step("third", "work.reply", "reply-third", work_id=WORK[0], meta="https://example.org/preparations/third")
    q.step("third", "work.reply", "reply-third-again", work_id=WORK[0])
    q.step("opener", "work.reply", "reply-opener", work_id=WORK[0], meta="the opener's preparation")
    q.step("third", "work.complete", "complete-by-preparer", work_id=WORK[0])
    q.step("opener", "work.cancel", "cancel-by-opener", work_id=WORK[0])
    q.step("other", "work.complete", "complete-unknown", work_id=WORK[8])
    q.step("other", "work.cancel", "cancel-unknown", work_id=WORK[8])
    q.step("other", "work.complete", "complete-w1", work_id=WORK[0], meta="done")
    q.step("other", "work.complete", "complete-again", work_id=WORK[0])
    q.step("other", "work.cancel", "cancel-completed", work_id=WORK[0])
    q.step("other", "work.ask", "ask-after-decision", work_id=WORK[0], preparer_id=UNISSUED)
    q.step("outsider", "work.reply", "reply-after-decision", work_id=WORK[0])
    q.step("opener", "work.create", "create-w2", work_id=WORK[1])
    q.step("opener", "work.assign", "assign-w2-to-self", work_id=WORK[1], assignee_id="$opener")
    q.step("opener", "work.cancel", "cancel-w2", work_id=WORK[1], meta="won't be done")
    q.step("opener", "work.complete", "complete-cancelled", work_id=WORK[1])
    q.step("opener", "work.create", "create-w3", work_id=WORK[2])
    q.step("opener", "work.assign", "assign-w3", work_id=WORK[2], assignee_id="$third")
    q.step("third", "work.complete", "complete-w3-without-preparers", work_id=WORK[2])
    q.step("other", "stream.close", "close-by-assignee")
    q.step("opener", "stream.close", "close")
    q.step("opener", "work.create", "create-after-close", work_id=WORK[3])
    out.append(q.reads())
    q = Sequence("work", "malformed", "what the engine does not read", who="third")
    q.invalid("third", "work.create", "work-id-missing")
    q.invalid("third", "work.create", "work-id-not-an-id", work_id="w1")
    q.invalid("third", "work.assign", "assignee-missing", work_id=WORK[0])
    q.invalid("third", "work.ask", "preparer-not-an-id", work_id=WORK[0], preparer_id=5)
    q.invalid("third", "work.reply", "unknown-param", work_id=WORK[0], preparer_id="$other")
    q.invalid("third", "work.complete", "meta-not-text", work_id=WORK[0], meta=[])
    q.step("third", "task.open", "foreign", task_id=TASK[0])
    q.step("third", "work.create", "create", work_id=WORK[0])
    q.step("third", "work.assign", "assign-to-unissued", work_id=WORK[0], assignee_id=UNISSUED)
    q.step("other", "work.ask", "ask-by-other", work_id=WORK[0], preparer_id="$opener")
    out.append(q.reads("opener"))
    return out


def tower_sequences():
    out = []
    q = Sequence("tower", "reviews", "the opener approves completed tasks; no close while a review is pending")
    task_story(q, approve=True)
    q.step("other", "review.approve", "approve-by-assignee", task_id=TASK[0])
    q.step("opener", "review.approve", "approve-unknown", task_id=TASK[8])
    q.step("other", "stream.close", "close-by-other-pending")
    q.step("opener", "stream.close", "close-pending")
    q.step("opener", "review.approve", "approve-t1", task_id=TASK[0], meta="good")
    q.step("opener", "review.approve", "approve-again", task_id=TASK[0])
    q.step("opener", "stream.close", "close-still-pending")
    q.step("opener", "review.approve", "approve-t2", task_id=TASK[1])
    q.step("opener", "log.append", "foreign", text="x")
    q.step("opener", "stream.close", "close-all-approved")
    q.step("opener", "review.approve", "approve-after-close", task_id=TASK[2])
    out.append(q.reads())
    q = Sequence("tower", "no-work", "a stream with no completed task closes")
    q.step("opener", "task.open", "open", task_id=TASK[0])
    q.step("opener", "task.assign", "assign", task_id=TASK[0], assignee_id="$third")
    q.invalid("opener", "review.approve", "task-not-an-id", task_id="x")
    q.step("opener", "stream.close", "close-with-open-work")
    out.append(q.reads())
    q = Sequence("tower", "malformed", "what the engine does not read")
    task_malformed(q)
    out.append(q.reads())
    return out


# -- generated sequences ----------------------------------------------------------------------------------------------

def generated(proof, count, seed):
    """`count` sequences of `proof`, drawn from a generator seeded with `seed`: commands of the proof (now and then one
    of another, or malformed params, or an actor_id that is not the caller's), by any of the roles, mostly the ones
    the rules let act, on a few tasks and principals."""
    rnd = random.Random(seed)
    cmds = [c for c in COMMANDS[proof] if c != "stream.open"]
    foreign = sorted({c for p in PROOFS for c in COMMANDS[p]} - set(COMMANDS[proof]) - {"stream.open"})
    out = []
    for k in range(count):
        opener = rnd.choice(["opener", "opener", "other", "third"])
        q = Sequence(proof, "g%02d" % (k + 1), "generated", who=opener)
        for _ in range(rnd.randint(4, 16)):
            roll = rnd.random()
            cmd = rnd.choice([c for c in cmds if c != "stream.close"] or cmds) if rnd.random() < 0.93 else \
                "stream.close"
            who = opener if rnd.random() < 0.6 else rnd.choice(ROLES)
            params = {}
            if cmd == "log.append":
                params["text"] = rnd.choice(["a line", "", "é and \t", "line %d" % rnd.randint(0, 99)])
            if cmd.startswith("principal."):
                params["principal_id"] = rnd.choice(["$" + r for r in ROLES] + [UNISSUED])
            if cmd.startswith("task.") or cmd == "review.approve":
                params["task_id"] = rnd.choice(TASK[:3])
            if cmd == "task.assign":
                params["assignee_id"] = rnd.choice(["$" + r for r in ROLES])
            if cmd == "task.complete":
                assignee = q.m.assignee(params["task_id"])
                if assignee and rnd.random() < 0.7:
                    who = assignee[1:]
            if cmd == "task.open" and rnd.random() < 0.3:
                params["parent_task_id"] = rnd.choice(TASK[:4])
            if cmd.startswith("work."):
                params["work_id"] = rnd.choice(WORK[:3])
                assignee = q.m.work_assignee(params["work_id"])
                if cmd == "work.assign":
                    params["assignee_id"] = rnd.choice(["$" + r for r in ROLES])
                if cmd == "work.ask":
                    params["preparer_id"] = rnd.choice(["$" + r for r in ROLES])
                if cmd in ("work.ask", "work.complete", "work.cancel") and assignee and rnd.random() < 0.7:
                    who = assignee[1:]
                if cmd == "work.reply":
                    asked = [p for w, p in q.m.asked if w == params["work_id"]]
                    if asked and rnd.random() < 0.7:
                        who = rnd.choice(asked)[1:]
            if rnd.random() < 0.15:
                params["meta"] = rnd.choice(["m", "", "a note"])
            if roll < 0.05:
                q.step(who, rnd.choice(foreign), "foreign", **params)
            elif roll < 0.09:
                bads = [{"extra": 1}, {"meta": 7}] + [{f: v} for f, v in (("task_id", "nope"), ("principal_id", "nope"),
                                                                        ("assignee_id", 5), ("text", None),
                                                                        ("work_id", "nope"), ("preparer_id", 5))
                                                      if f in params]
                q.invalid(who, cmd, "malformed", **dict(params, **rnd.choice(bads)))
            elif roll < 0.13:
                other = rnd.choice([r for r in ROLES if r != who])
                q.step(who, cmd, "actor-id-other", actor_id="$" + other, **params)
            elif roll < 0.18:
                q.step(who, cmd, "actor-id-own", actor_id="$" + who, **params)
            else:
                q.step(who, cmd, None, **params)
        if rnd.random() < 0.5:
            q.step(opener, "stream.close", "close")
        out.append(q.reads(rnd.choice(ROLES)))
    return out


GENERATED = {"core": 40, "log": 60, "principals": 100, "tasks": 100, "work": 100, "tower": 100}
HAND = {"core": core_sequences, "log": log_sequences, "principals": principals_sequences, "tasks": tasks_sequences,
        "work": work_sequences, "tower": tower_sequences}


def proof_theme(proof):
    seqs = HAND[proof]() + generated(proof, GENERATED[proof], "provenstream-conformance:" + proof)
    return [c for q in seqs for c in q.cases]


# -- the host's own themes --------------------------------------------------------------------------------------------

def me(p):
    return ok({"principal_id": p})


def open_(name, who="opener", bind="s", chain="c0", meta=None, proof="core", **extra):
    params = {"proof_revision_url": "$url_" + proof}
    if meta is not None:
        params["meta"] = meta
    ev = {"event": "stream.opened", "stream_id": "$uuid:" + bind, "actor_id": "$" + who, "meta": meta,
          "proof_revision_url": "$url_" + proof}
    if proof != "core":
        extra = dict(extra, proof=proof)
    return call(name, who, "stream.open", params, accepted(0, ev, "$hex64:" + chain), **extra)


def ev_close(s, actor="$opener", meta=None):
    return {"event": "stream.closed", "stream_id": s, "actor_id": actor, "meta": meta}


def ev_append(s, text, actor="$opener", meta=None):
    return {"event": "log.appended", "stream_id": s, "actor_id": actor, "meta": meta, "text": text}


def ev_open(s, actor="$opener", meta=None, proof="core"):
    return {"event": "stream.opened", "stream_id": s, "actor_id": actor, "meta": meta,
            "proof_revision_url": "$url_" + proof}


def auth():
    """Who is asking: a token names its caller; no token or an unknown one is unauthorized, and so is a proof command
    asked without one; a name that is no method is method_not_found before anyone is asked for a token."""
    return [
        call("whoami-opener", "opener", "whoami", {}, me("$opener")),
        call("whoami-other", "other", "whoami", {}, me("$other")),
        call("whoami-third", "third", "whoami", {}, me("$third")),
        call("whoami-outsider", "outsider", "whoami", {}, me("$outsider")),
        call("whoami-no-token", "none", "whoami", {}, UNAUTHORIZED),
        call("whoami-unknown-token", "unknown", "whoami", {}, UNAUTHORIZED),
        call("revisions-list-no-token", "none", "revisions.list", {}, UNAUTHORIZED),
        call("rpc-discover-unknown-token", "unknown", "rpc.discover", {}, UNAUTHORIZED),
        call("stream-get-no-token", "none", "stream.get", {"stream_id": NOWHERE}, UNAUTHORIZED),
        call("stream-get-bad-params-no-token", "none", "stream.get", {}, UNAUTHORIZED),
        call("usage-get-unknown-token", "unknown", "usage.get", {}, UNAUTHORIZED),
        call("principal-create-no-token", "none", "principal.create", {}, UNAUTHORIZED),
        call("principal-create-unknown-token", "unknown", "principal.create", {}, UNAUTHORIZED),
        call("stream-open-no-token", "none", "stream.open", {"proof_revision_url": "$url_core"}, UNAUTHORIZED),
        call("stream-open-unknown-token", "unknown", "stream.open", {"proof_revision_url": "$url_core"},
             UNAUTHORIZED),
        call("stream-close-unknown-token", "unknown", "stream.close", {"stream_id": NOWHERE}, UNAUTHORIZED),
        call("dotted-unknown-method-no-token", "none", "no.such", {}, UNAUTHORIZED),
        call("not-a-method-no-token", "none", "nonsense", {}, err("method_not_found")),
        call("not-a-method-unknown-token", "unknown", "nonsense", {}, err("method_not_found")),
    ]


def parse():
    """Messages as bytes: strict JSON, one JSON-RPC 2.0 request object, ids echoed when valid."""
    m = me("$opener")
    return [
        raw("not-json", "{not json", err("parse_error", detail=DETAIL)),
        raw("empty-object-truncated", '{"jsonrpc":"2.0","id":1,"method":"whoami"', err("parse_error", detail=DETAIL)),
        raw("repeated-key", '{"jsonrpc":"2.0","id":1,"id":2,"method":"whoami"}', err("parse_error", detail=DETAIL)),
        raw("repeated-key-in-params", '{"jsonrpc":"2.0","id":1,"method":"whoami","params":{"a":1,"a":2}}',
            err("parse_error", detail=DETAIL)),
        raw("nan", '{"jsonrpc":"2.0","id":1,"method":"whoami","params":{"x":NaN}}', err("parse_error", detail=DETAIL)),
        raw("infinity", '{"jsonrpc":"2.0","id":1,"method":"whoami","params":{"x":Infinity}}',
            err("parse_error", detail=DETAIL)),
        raw("number-overflow", '{"jsonrpc":"2.0","id":1,"method":"whoami","params":{"x":1e999}}',
            err("parse_error", detail=DETAIL)),
        raw("lone-surrogate", '{"jsonrpc":"2.0","id":1,"method":"whoami","params":{"x":"\\ud800"}}',
            err("parse_error", detail=DETAIL)),
        raw("not-utf8", None, err("parse_error", detail=DETAIL),
            raw_base64=base64.b64encode(b'{"jsonrpc":"2.0","id":1,"method":"\xff"}').decode()),
        raw("batch-empty", "[]", err("invalid_request", detail=DETAIL)),
        raw("batch-of-one", '[{"jsonrpc":"2.0","id":1,"method":"whoami"}]', err("invalid_request", detail=DETAIL)),
        raw("a-string", '"whoami"', err("invalid_request", detail=DETAIL)),
        raw("a-number", "42", err("invalid_request", detail=DETAIL)),
        raw("null", "null", err("invalid_request", detail=DETAIL)),
        raw("notification", '{"jsonrpc":"2.0","method":"whoami"}', err("invalid_request", detail=DETAIL)),
        raw("id-fraction", '{"jsonrpc":"2.0","id":1.5,"method":"whoami"}', err("invalid_request", detail=DETAIL)),
        raw("id-object", '{"jsonrpc":"2.0","id":{"n":1},"method":"whoami"}', err("invalid_request", detail=DETAIL)),
        raw("id-boolean", '{"jsonrpc":"2.0","id":true,"method":"whoami"}', err("invalid_request", detail=DETAIL)),
        raw("version-1", '{"jsonrpc":"1.0","id":7,"method":"whoami"}', err("invalid_request", detail=DETAIL), 7),
        raw("no-version", '{"id":8,"method":"whoami"}', err("invalid_request", detail=DETAIL), 8),
        raw("method-not-a-string", '{"jsonrpc":"2.0","id":9,"method":5}', err("invalid_request", detail=DETAIL), 9),
        raw("no-method", '{"jsonrpc":"2.0","id":10}', err("invalid_request", detail=DETAIL), 10),
        raw("extra-member", '{"jsonrpc":"2.0","id":11,"method":"whoami","extra":1}',
            err("invalid_request", detail=DETAIL), 11),
        raw("params-array", '{"jsonrpc":"2.0","id":12,"method":"whoami","params":[]}', bad_params(), 12),
        raw("params-string", '{"jsonrpc":"2.0","id":13,"method":"whoami","params":"x"}', bad_params(), 13),
        raw("params-null", '{"jsonrpc":"2.0","id":14,"method":"whoami","params":null}', bad_params(), 14),
        raw("params-absent", '{"jsonrpc":"2.0","id":15,"method":"whoami"}', m, 15),
        raw("id-string", '{"jsonrpc":"2.0","id":"a b","method":"whoami","params":{}}', m, "a b"),
        raw("id-null", '{"jsonrpc":"2.0","id":null,"method":"whoami","params":{}}', m, None),
        raw("id-negative", '{"jsonrpc":"2.0","id":-5,"method":"whoami","params":{}}', m, -5),
        raw("id-large", '{"jsonrpc":"2.0","id":1152921504606846976,"method":"whoami"}', m, 1152921504606846976),
        raw("member-order", '{"params":{},"method":"whoami","id":16,"jsonrpc":"2.0"}', m, 16),
        raw("surrounding-space", '  {"jsonrpc":"2.0","id":17,"method":"whoami"}  ', m, 17),
        raw("escaped-method", '{"jsonrpc":"2.0","id":18,"method":"who\\u0061mi"}', m, 18),
        raw("over-one-mebibyte", None, err("invalid_request", detail=DETAIL), oversize=True),
        raw("after-over-long", '{"jsonrpc":"2.0","id":19,"method":"whoami"}', m, 19),
        raw("unknown-param-key", '{"jsonrpc":"2.0","id":20,"method":"whoami","params":{"x":"é"}}',
            bad_params(), 20),
        raw("params-in-a-proof-command", '{"jsonrpc":"2.0","id":21,"method":"stream.open","params":[]}', bad_params(),
            21),
    ]


def reads():
    """The stream's queries: reading is unrestricted, so any principal reads any stream, opened by anyone; a stream
    with no rows is stream_must_exist. `revision.events` reads across every stream of a revision, which other sessions
    share (the three carriers of a compared run, the other themes), so what it answers is checked by shape: a page of
    events of one revision, each with its stream, seq and chain head, and a position or null; a name no event of the
    revision has answers none; a revision with no engine is revision_must_be_installed, and a revision, event name,
    position or limit of the wrong form is invalid_params."""
    s = "$s"
    notes = {"$open": True}
    view = lambda closed=False: {"stream_id": s, "proof_revision_url": "$url_core", "opener_id": "$opener",
                                 "closed": closed}
    R = "$rev_core"
    any_event = {"$open": True, "event": "$string", "stream_id": "$uuid", "actor_id": "$uuid", "seq": "$int",
                 "chain": "$hex64"}
    an_open = dict(any_event, event="stream.opened", seq=0, meta="$any", proof_revision_url="$url_core")
    return [
        open_("open"),
        call("get-by-opener", "opener", "stream.get", {"stream_id": s}, ok(view())),
        call("get-by-outsider", "outsider", "stream.get", {"stream_id": s}, ok(view())),
        call("head-by-outsider", "outsider", "stream.head", {"stream_id": s},
             ok({"stream_id": s, "length": 1, "chain": "$c0"})),
        call("events-by-third", "third", "stream.events", {"stream_id": s},
             ok({"stream_id": s, "events": [dict(ev_open(s), seq=0, chain="$c0")], "next": None})),
        dict(call("rows-by-other", "other", "stream.rows", {"stream_id": s}, ok({"stream_id": s, "rows": [
            {"seq": 0, "request": "$any", "event": "$any", "meta_salt": "$any", "chain": "$c0"}],
            "next": None})), check="chain"),
        call("describe-by-outsider", "outsider", "stream.describe", {"stream_id": s}, ok(described("core"))),
        call("revision-events-first", "outsider", "revision.events", {"revision": R, "limit": 1},
             ok({"revision": R, "events": [an_open], "next": "$int"})),
        call("revision-events-first-open", "third", "revision.events",
             {"revision": R, "event": "stream.opened", "limit": 1}, ok({"revision": R, "events": [an_open], "next": "$int"})),
        call("revision-events-a-page", "other", "revision.events", {"revision": R, "limit": 3},
             ok({"revision": R, "events": [an_open, any_event, any_event], "next": "$int"})),
        call("revision-events-of-no-such-name", "third", "revision.events", {"revision": R, "event": "stream.nothing"},
             ok({"revision": R, "events": [], "next": None})),
        call("revision-events-of-another-proof", "third", "revision.events", {"revision": R, "event": "log.appended"},
             ok({"revision": R, "events": [], "next": None})),
        call("revision-events-unknown-revision", "opener", "revision.events", {"revision": NO_COMMIT},
             refused("revision_must_be_installed")),
        call("revision-events-unknown-package", "outsider", "revision.events",
             {"revision": "${commit}/examples/nothing"}, refused("revision_must_be_installed")),
        call("revision-events-short-revision", "opener", "revision.events", {"revision": "abc1234"}, bad_params()),
        call("revision-events-by-url", "opener", "revision.events", {"revision": "$url_core"}, bad_params()),
        call("revision-events-missing-revision", "opener", "revision.events", {}, bad_params()),
        call("revision-events-bad-event-name", "opener", "revision.events", {"revision": R, "event": "opened"},
             bad_params()),
        call("revision-events-from-text", "opener", "revision.events", {"revision": R, "from": "1"}, bad_params()),
        call("revision-events-from-negative", "opener", "revision.events", {"revision": R, "from": -1}, bad_params()),
        call("revision-events-limit-0", "opener", "revision.events", {"revision": R, "limit": 0}, bad_params()),
        call("revision-events-limit-over", "opener", "revision.events", {"revision": R, "limit": 1001}, bad_params()),
        call("revision-events-unknown-key", "opener", "revision.events", {"revision": R, "stream_id": s},
             bad_params()),
        call("revision-events-where-is-no-param", "opener", "revision.events",
             {"revision": R, "where": {"stream_id": s}}, bad_params()),
        call("usage-by-outsider", "outsider", "usage.get", {"scope": "stream", "key": s},
             ok({"usage": "$any", "notes": notes})),
        call("usage-per-revision", "third", "usage.get", {"scope": "revision"}, ok({"usage": "$any", "notes": notes})),
        call("usage-of-a-revision", "third", "usage.get", {"scope": "revision", "key": "$rev_core"},
             ok({"usage": "$any", "notes": notes})),
        call("usage-default", "outsider", "usage.get", {}, ok({"usage": "$any", "notes": notes})),
        call("usage-key-without-scope", "opener", "usage.get", {"key": s}, bad_params()),
        call("usage-stream-without-key", "opener", "usage.get", {"scope": "stream"}, bad_params()),
        call("usage-unknown-scope", "opener", "usage.get", {"scope": "everything"}, bad_params()),
        call("usage-of-unknown-stream", "opener", "usage.get", {"scope": "stream", "key": NOWHERE},
             refused("stream_must_exist")),
        call("usage-of-a-stream-not-an-id", "opener", "usage.get", {"scope": "stream", "key": "S"},
             refused("stream_must_exist")),
        call("get-unknown-stream", "opener", "stream.get", {"stream_id": NOWHERE}, refused("stream_must_exist")),
        call("head-unknown-stream", "outsider", "stream.head", {"stream_id": NOWHERE}, refused("stream_must_exist")),
        call("events-unknown-stream", "opener", "stream.events", {"stream_id": NOWHERE},
             refused("stream_must_exist")),
        call("rows-unknown-stream", "opener", "stream.rows", {"stream_id": NOWHERE}, refused("stream_must_exist")),
        call("describe-unknown-stream", "opener", "stream.describe", {"stream_id": NOWHERE},
             refused("stream_must_exist")),
        call("get-without-stream", "opener", "stream.get", {}, bad_params()),
        call("get-old-param-name", "opener", "stream.get", {"stream": s}, bad_params()),
        call("get-stream-not-an-id", "opener", "stream.get", {"stream_id": "S"}, bad_params()),
        call("get-stream-uppercase", "opener", "stream.get", {"stream_id": NOWHERE.upper().replace("0", "A")},
             bad_params()),
        call("get-unknown-key", "opener", "stream.get", {"stream_id": s, "from": 0}, bad_params()),
        call("head-unknown-key", "opener", "stream.head", {"stream_id": s, "x": 1}, bad_params()),
        call("whoami-with-params", "opener", "whoami", {"x": 1}, bad_params()),
        call("close", "opener", "stream.close", {"stream_id": s}, accepted(1, ev_close(s), "$hex64:c1")),
        call("get-after-close", "outsider", "stream.get", {"stream_id": s}, ok(view(True))),
        call("head-after-close", "third", "stream.head", {"stream_id": s},
             ok({"stream_id": s, "length": 2, "chain": "$c1"})),
        open_("open-by-outsider", who="outsider", bind="s2", chain="d0", proof="log"),
        call("get-by-another", "opener", "stream.get", {"stream_id": "$s2"},
             ok({"stream_id": "$s2", "proof_revision_url": "$url_log", "opener_id": "$outsider", "closed": False}),
             proof="log"),
    ]


def paging():
    """`stream.events` and `stream.rows` page from `from`, at most `limit` (1 to 1000), with `next`; `revision.events`
    pages the same way by position: a page's `next` is the `from` of the next, and the pages of one event name of the
    log revision end with null (checked by shape: the revision's streams are shared with other sessions)."""
    s = "$s"
    texts = ["one", "two", "three"]
    events = [dict(ev_open(s, proof="log"), seq=0, chain="$c0")] + \
        [dict(ev_append(s, t), seq=i + 1, chain="$c%d" % (i + 1)) for i, t in enumerate(texts)]
    row = lambda i: {"seq": i, "request": "$any", "event": "$any", "meta_salt": "$any", "chain": "$c%d" % i}
    page = lambda evs, nxt: ok({"stream_id": s, "events": evs, "next": nxt})
    rows = lambda rs, nxt: ok({"stream_id": s, "rows": rs, "next": nxt})
    P = dict(proof="log")
    return [open_("open", proof="log")] + [
        call("append-%d" % (i + 1), "opener", "log.append", {"stream_id": s, "text": t},
             accepted(i + 1, ev_append(s, t), "$hex64:c%d" % (i + 1)), **P) for i, t in enumerate(texts)] + [
        call("events-whole", "opener", "stream.events", {"stream_id": s}, page(events, None), **P),
        call("events-limit-1", "opener", "stream.events", {"stream_id": s, "limit": 1}, page(events[:1], 1), **P),
        call("events-from-1-limit-2", "third", "stream.events", {"stream_id": s, "from": 1, "limit": 2},
             page(events[1:3], 3), **P),
        call("events-from-3-limit-2", "third", "stream.events", {"stream_id": s, "from": 3, "limit": 2},
             page(events[3:], None), **P),
        call("events-limit-exactly-the-length", "opener", "stream.events", {"stream_id": s, "limit": 4},
             page(events, None), **P),
        call("events-limit-3", "opener", "stream.events", {"stream_id": s, "limit": 3}, page(events[:3], 3), **P),
        call("events-from-the-length", "opener", "stream.events", {"stream_id": s, "from": 4}, page([], None), **P),
        call("events-from-past-the-end", "opener", "stream.events", {"stream_id": s, "from": 99}, page([], None),
             **P),
        call("events-from-2", "other", "stream.events", {"stream_id": s, "from": 2}, page(events[2:], None), **P),
        call("events-limit-most", "opener", "stream.events", {"stream_id": s, "limit": 1000}, page(events, None),
             **P),
        call("events-limit-0", "opener", "stream.events", {"stream_id": s, "limit": 0}, bad_params(), **P),
        call("events-limit-over", "opener", "stream.events", {"stream_id": s, "limit": 1001}, bad_params(), **P),
        call("events-from-negative", "opener", "stream.events", {"stream_id": s, "from": -1}, bad_params(), **P),
        call("events-from-text", "opener", "stream.events", {"stream_id": s, "from": "1"}, bad_params(), **P),
        call("events-from-fraction", "opener", "stream.events", {"stream_id": s, "from": 1.5}, bad_params(), **P),
        call("events-limit-boolean", "opener", "stream.events", {"stream_id": s, "limit": True}, bad_params(), **P),
        call("events-from-null", "opener", "stream.events", {"stream_id": s, "from": None}, bad_params(), **P),
        dict(call("rows-whole", "third", "stream.rows", {"stream_id": s}, rows([row(i) for i in range(4)], None),
                  **P), check="chain"),
        call("rows-limit-2", "third", "stream.rows", {"stream_id": s, "limit": 2}, rows([row(0), row(1)], 2), **P),
        call("rows-from-2", "third", "stream.rows", {"stream_id": s, "from": 2}, rows([row(2), row(3)], None), **P),
        call("rows-from-3-limit-1", "third", "stream.rows", {"stream_id": s, "from": 3, "limit": 1},
             rows([row(3)], None), **P),
        call("rows-from-past-the-end", "third", "stream.rows", {"stream_id": s, "from": 5}, rows([], None), **P),
        call("rows-limit-over", "third", "stream.rows", {"stream_id": s, "limit": 5000}, bad_params(), **P),
    ] + revision_paging(P)


def revision_paging(P):
    R = "$rev_log"
    appended = {"$open": True, "event": "log.appended", "stream_id": "$uuid", "actor_id": "$uuid", "seq": "$int",
                "chain": "$hex64", "text": "$string"}
    return [
        call("revision-events-appended-limit-2", "third", "revision.events",
             {"revision": R, "event": "log.appended", "limit": 2},
             ok({"revision": R, "events": [appended, appended], "next": "$int:cur"}), **P),
        call("revision-events-appended-from-next", "third", "revision.events",
             {"revision": R, "event": "log.appended", "from": "$cur", "limit": 1},
             ok({"revision": R, "events": [appended], "next": "$int"}), **P),
        call("revision-events-from-far-past-the-end", "opener", "revision.events",
             {"revision": R, "event": "log.appended", "from": 10 ** 12},
             ok({"revision": R, "events": [], "next": None}), **P),
    ]


def idempotency():
    """An `idempotency_key` makes a retry by the same caller answer the first answer; the same key with another
    request is `idempotency_key_must_match_its_request`; the same key from another caller is another write. Keys carry
    the run's nonce (`${run}`), so a second run against the same host starts afresh."""
    s = "$s"
    key = "key-${run}"
    P = dict(proof="log")
    return [
        call("open-with-key", "opener", "stream.open",
             {"proof_revision_url": "$url_log", "meta": "idempotent", "idempotency_key": "open-${run}"},
             accepted(0, ev_open("$uuid:s", meta="idempotent", proof="log"), "$hex64:c0"), **P),
        call("open-retried", "opener", "stream.open",
             {"proof_revision_url": "$url_log", "meta": "idempotent", "idempotency_key": "open-${run}"},
             accepted(0, ev_open(s, meta="idempotent", proof="log"), "$c0"), **P),
        call("open-retried-with-actor-id", "opener", "stream.open",
             {"proof_revision_url": "$url_log", "meta": "idempotent", "idempotency_key": "open-${run}",
              "actor_id": "$opener"},
             accepted(0, ev_open(s, meta="idempotent", proof="log"), "$c0"), **P),
        call("open-retried-other-meta", "opener", "stream.open",
             {"proof_revision_url": "$url_log", "meta": "other", "idempotency_key": "open-${run}"},
             refused("idempotency_key_must_match_its_request"), **P),
        call("open-same-key-other-caller", "other", "stream.open",
             {"proof_revision_url": "$url_log", "meta": "idempotent", "idempotency_key": "open-${run}"},
             accepted(0, ev_open("$uuid:s2", "$other", "idempotent", proof="log"), "$hex64:d0"), **P),
        call("append-with-key", "opener", "log.append", {"stream_id": s, "text": "once", "idempotency_key": key},
             accepted(1, ev_append(s, "once"), "$hex64:c1"), **P),
        call("append-retried", "opener", "log.append", {"stream_id": s, "text": "once", "idempotency_key": key},
             accepted(1, ev_append(s, "once"), "$c1"), **P),
        call("append-retried-null-meta", "opener", "log.append",
             {"stream_id": s, "text": "once", "meta": None, "idempotency_key": key},
             accepted(1, ev_append(s, "once"), "$c1"), **P),
        call("same-key-other-text", "opener", "log.append", {"stream_id": s, "text": "twice", "idempotency_key": key},
             refused("idempotency_key_must_match_its_request"), **P),
        call("same-key-other-command", "opener", "stream.close", {"stream_id": s, "idempotency_key": key},
             refused("idempotency_key_must_match_its_request"), **P),
        call("same-key-other-caller", "other", "log.append", {"stream_id": "$s2", "text": "once",
                                                              "idempotency_key": key},
             accepted(1, ev_append("$s2", "once", "$other"), "$hex64:d1"), **P),
        call("other-caller-retried", "other", "log.append", {"stream_id": "$s2", "text": "once",
                                                             "idempotency_key": key},
             accepted(1, ev_append("$s2", "once", "$other"), "$d1"), **P),
        call("refused-with-key", "third", "log.append",
             {"stream_id": s, "text": "x", "idempotency_key": "refused-${run}"}, refused("only_opener_can_append"),
             **P),
        call("refused-retried", "third", "log.append",
             {"stream_id": s, "text": "x", "idempotency_key": "refused-${run}"}, refused("only_opener_can_append"),
             **P),
        call("key-empty", "opener", "stream.close", {"stream_id": s, "idempotency_key": ""}, bad_params(), **P),
        call("key-too-long", "opener", "stream.close", {"stream_id": s, "idempotency_key": "${run}" + "x" * 165},
             bad_params(), **P),
        call("key-not-text", "opener", "stream.close", {"stream_id": s, "idempotency_key": 5}, bad_params(), **P),
        call("head-unchanged", "opener", "stream.head", {"stream_id": s},
             ok({"stream_id": s, "length": 2, "chain": "$c1"}), **P),
        call("key-longest", "opener", "stream.close", {"stream_id": s, "idempotency_key": "${run}" + "x" * 164},
             accepted(2, ev_close(s), "$hex64:c2"), **P),
        call("key-longest-retried", "opener", "stream.close", {"stream_id": s, "idempotency_key": "${run}" + "x" * 164},
             accepted(2, ev_close(s), "$c2"), **P),
        call("close-again-without-key", "opener", "stream.close", {"stream_id": s}, refused("stream_must_be_open"),
             **P),
        call("events", "opener", "stream.events", {"stream_id": s}, ok({"stream_id": s, "events": [
            dict(ev_open(s, meta="idempotent", proof="log"), seq=0, chain="$c0"),
            dict(ev_append(s, "once"), seq=1, chain="$c1"),
            dict(ev_close(s), seq=2, chain="$c2")], "next": None}), **P),
    ]


def actor():
    """`actor_id`: the host fills it in from the token, accepts the caller's own, and refuses any other
    (`actor_id_must_match_the_token`) before it asks the proof anything."""
    s = "$s"
    return [
        call("open-with-own-actor-id", "opener", "stream.open", {"proof_revision_url": "$url_core",
                                                                 "actor_id": "$opener"},
             accepted(0, ev_open("$uuid:s"), "$hex64:c0")),
        call("open-with-another-actor-id", "opener", "stream.open", {"proof_revision_url": "$url_core",
                                                                     "actor_id": "$other"},
             refused("actor_id_must_match_the_token")),
        call("open-as-an-unissued-actor", "other", "stream.open", {"proof_revision_url": "$url_core",
                                                                   "actor_id": UNISSUED},
             refused("actor_id_must_match_the_token")),
        call("close-claiming-the-opener", "other", "stream.close", {"stream_id": s, "actor_id": "$opener"},
             refused("actor_id_must_match_the_token")),
        call("close-as-itself", "other", "stream.close", {"stream_id": s, "actor_id": "$other"},
             refused("only_opener_can_close")),
        call("before-the-stream-is-asked", "other", "stream.close", {"stream_id": NOWHERE, "actor_id": "$opener"},
             refused("actor_id_must_match_the_token")),
        call("actor-id-not-an-id", "opener", "stream.close", {"stream_id": s, "actor_id": "me"}, bad_params()),
        call("actor-id-null", "opener", "stream.close", {"stream_id": s, "actor_id": None}, bad_params()),
        call("actor-id-uppercase", "opener", "stream.close", {"stream_id": s, "actor_id": UNISSUED.replace("0", "A")},
             bad_params()),
        call("actor-id-on-a-query", "opener", "stream.head", {"stream_id": s, "actor_id": "$opener"}, bad_params()),
        call("actor-id-with-key", "opener", "stream.close",
             {"stream_id": s, "actor_id": "$other", "idempotency_key": "actor-${run}"},
             refused("actor_id_must_match_the_token")),
        call("close-with-own-actor-id", "opener", "stream.close", {"stream_id": s, "actor_id": "$opener"},
             accepted(1, ev_close(s), "$hex64:c1")),
        call("events", "outsider", "stream.events", {"stream_id": s}, ok({"stream_id": s, "events": [
            dict(ev_open(s), seq=0, chain="$c0"), dict(ev_close(s), seq=1, chain="$c1")], "next": None})),
    ]


def discovery():
    """`rpc.discover` (OpenRPC), `revision.describe`, `revisions.list`: what a host says it serves, each of the five
    proofs a revision of one commit."""
    method = lambda name, kind: {"$open": True, "name": name, "x-provenstream-kind": kind}
    queries = ["revision.describe", "revision.events", "revisions.list", "rpc.discover", "stream.describe",
               "stream.events", "stream.get", "stream.head", "stream.rows", "usage.get", "whoami"]
    errors = {c: {"$open": True, "code": rpc, "message": m, "data": {"code": c}} for c, (rpc, m) in TABLE.items()}
    proof_commands = sorted({c for p in PROOFS for c in COMMANDS[p]})
    doc = {"$open": True, "openrpc": "1.3.2",
           "info": {"$open": True, "title": "Provenstream host", "version": "$string"},
           "x-provenstream-protocol": PROTOCOL,
           "x-provenstream-revisions": {"$contains": [{"revision": "$rev_" + p, "protocol": PROTOCOL}
                                                      for p in PROOFS]},
           "methods": {"$contains": [method(q, "query") for q in queries] +
                       [method(h, "host_command") for h in ("principal.create", "token.rotate")] +
                       [method(c, "proof_command") for c in proof_commands]},
           "components": {"$open": True, "errors": errors}}
    listed = lambda p: {"revision": "$rev_" + p, "commit": "$commit", "package": PACKAGES[p], "running": "$any"}
    out = [
        call("discover", "opener", "rpc.discover", {}, ok(doc), proof=list(PROOFS)),
        call("discover-the-commands", "outsider", "rpc.discover", {}, ok({"$open": True, "methods": {"$contains": [
            {"$open": True, "name": "task.open", "x-provenstream-who": "the stream's opener",
             "x-provenstream-event": {"name": "task.opened", "fields": EV + ["task_id", "parent_task_id"]},
             "x-provenstream-rules": SPEC["tasks"]["task.open"]["rules"],
             "x-provenstream-revisions": {"$contains": ["$rev_tasks", "$rev_tower"]}},
            {"$open": True, "name": "stream.close",
             "x-provenstream-variants": {"$contains": [
                 {"$open": True, "rules": SPEC["tower"]["stream.close"]["rules"], "revisions": ["$rev_tower"]},
                 {"$open": True, "rules": SPEC["core"]["stream.close"]["rules"]}]}}]}}),
             proof=["tasks", "tower"]),
        call("discover-by-outsider", "outsider", "rpc.discover", {},
             ok({"$open": True, "x-provenstream-protocol": PROTOCOL})),
        call("discover-without-params", "third", "rpc.discover", None, ok({"$open": True, "openrpc": "1.3.2"})),
        call("discover-with-params", "opener", "rpc.discover", {"x": 1}, bad_params()),
        call("discover-lists-the-broken-engines", "opener", "rpc.discover", {},
             ok({"$open": True, "x-provenstream-revisions-unavailable": {"$contains": ["$broken", "$notiface"]}}),
             local_only=True),
        call("revision-describe-short", "opener", "revision.describe", {"revision": "abc1234"}, bad_params()),
        call("revision-describe-missing", "opener", "revision.describe", {}, bad_params()),
        call("revision-describe-unknown", "outsider", "revision.describe", {"revision": NO_COMMIT},
             refused("revision_must_be_installed")),
        call("revision-describe-unknown-package", "outsider", "revision.describe",
             {"revision": "${commit}/examples/nothing"}, refused("revision_must_be_installed")),
        call("revision-describe-bad-package", "outsider", "revision.describe", {"revision": "${commit}/a//b"},
             bad_params()),
        call("revisions-list", "third", "revisions.list", {},
             ok({"revisions": {"$contains": [listed(p) for p in PROOFS]}}), proof=list(PROOFS)),
        call("revisions-list-with-params", "third", "revisions.list", {"all": True}, bad_params()),
    ]
    for p in PROOFS:
        out.append(call("revision-describe-" + p, "outsider", "revision.describe", {"revision": "$rev_" + p},
                        ok(described(p)), proof=p))
    return out


def host_commands():
    """The host's commands: `principal.create` for any signed-in principal (re-issuing a token for a given id is the
    operator's only), `token.rotate` the caller's own (run only against a host the runner made, on a principal it
    issued for the run: a remote run never rotates a token)."""
    return [
        call("principal-create", "opener", "principal.create", {},
             ok({"principal_id": "$uuid:new_p", "token": "$string:new_token"})),
        call("new-principal-whoami", "$new_token", "whoami", {}, me("$new_p")),
        call("new-principal-creates-another", "$new_token", "principal.create", {},
             ok({"principal_id": "$uuid:newer_p", "token": "$string:newer_token"})),
        call("newer-principal-whoami", "$newer_token", "whoami", {}, me("$newer_p")),
        call("new-principal-opens", "$new_token", "stream.open", {"proof_revision_url": "$url_core"},
             accepted(0, ev_open("$uuid:s", "$new_p"), "$hex64:c0")),
        call("new-principal-closes", "$new_token", "stream.close", {"stream_id": "$s"},
             accepted(1, ev_close("$s", "$new_p"), "$hex64:c1")),
        call("reissue-by-token", "opener", "principal.create", {"principal_id": "$new_p"},
             refused("only_the_operator_can_reissue_a_principal")),
        call("reissue-unissued-by-token", "outsider", "principal.create", {"principal_id": UNISSUED},
             refused("only_the_operator_can_reissue_a_principal")),
        call("principal-create-not-an-id", "opener", "principal.create", {"principal_id": "ann"}, bad_params()),
        call("principal-create-old-params", "opener", "principal.create", {"kind": "person"}, bad_params()),
        call("principal-create-unknown-param", "opener", "principal.create", {"x": 1}, bad_params()),
        call("token-rotate-no-token", "none", "token.rotate", {}, UNAUTHORIZED),
        call("token-rotate-unknown-token", "unknown", "token.rotate", {}, UNAUTHORIZED),
        call("spare-whoami", "spare", "whoami", {}, me("$spare"), local_only=True),
        call("token-rotate-with-params", "spare", "token.rotate", {"x": 1}, bad_params(), local_only=True),
        call("token-rotate", "spare", "token.rotate", {}, ok({"token": "$string:spare_token"}), local_only=True),
        call("old-token-after-rotate", "spare", "whoami", {}, UNAUTHORIZED, local_only=True),
        call("new-token-after-rotate", "$spare_token", "whoami", {}, me("$spare"), local_only=True),
    ]


def errors():
    """Names that are no method, a URL that is no revision URL (the core's `revision_url_must_name_a_commit`, applied by
    the host as the core reads it), the host's own refusals (`stream_must_exist`, `revision_must_be_installed`,
    `repository_must_match_the_engine`, `engine_must_implement_the_interface`), and `unavailable`, which only a host the
    runner made can be brought to (a revision whose engine is missing)."""
    s = "$s"
    nf = err("method_not_found")
    return [
        call("not-a-method", "opener", "nonsense", {}, nf),
        call("uppercase-method", "opener", "Stream.Open", {"proof_revision_url": "$url_core"}, nf),
        call("trailing-dot", "opener", "stream.", {}, nf),
        call("empty-method", "opener", "", {}, nf),
        call("method-with-space", "opener", "rpc.discover ", {}, nf),
        call("rpc-prefix", "opener", "rpc.other", {}, bad_params()),
        call("old-host-method", "opener", "principal.admin", {"stream_id": NOWHERE, "principal_id": "$other"},
             refused("stream_must_exist")),
        open_("open"),
        call("layer-command-on-core-stream", "opener", "task.open", {"stream_id": s, "task_id": NOWHERE}, NOT_FOUND),
        call("unknown-command-on-core-stream", "opener", "no.such", {"stream_id": s}, NOT_FOUND),
        call("unknown-command-without-stream", "opener", "no.such", {}, bad_params()),
        call("unknown-command-old-stream-param", "opener", "stream.close", {"stream": s}, bad_params()),
        call("unknown-command-on-unknown-stream", "opener", "no.such", {"stream_id": NOWHERE},
             refused("stream_must_exist")),
        call("command-key-in-params", "opener", "stream.close", {"stream_id": s, "command": "stream.close"},
             bad_params()),
        call("open-without-url", "opener", "stream.open", {}, bad_params()),
        call("open-url-not-a-string", "opener", "stream.open", {"proof_revision_url": 5}, bad_params()),
        call("open-url-null", "opener", "stream.open", {"proof_revision_url": None}, bad_params()),
        call("open-url-nul", "opener", "stream.open", {"proof_revision_url": "${repo}/commit/${commit}\u0000"},
             bad_params()),
        call("open-url-not-a-revision", "opener", "stream.open", {"proof_revision_url": 'not a url'},
             refused("revision_url_must_name_a_commit")),
        call("open-url-empty", "opener", "stream.open", {"proof_revision_url": ''},
             refused("revision_url_must_name_a_commit")),
        call("open-url-short-commit", "opener", "stream.open", {"proof_revision_url": '${repo}/commit/abc1234'},
             refused("revision_url_must_name_a_commit")),
        call("open-url-uppercase-commit", "opener", "stream.open",
             {"proof_revision_url": "${repo}/commit/" + UPPER_COMMIT}, refused("revision_url_must_name_a_commit")),
        call("open-url-trailing-space", "opener", "stream.open", {"proof_revision_url": '${repo}/commit/${commit} '},
             refused("revision_url_must_name_a_commit")),
        call("open-url-control-character", "opener", "stream.open", {"proof_revision_url": "${repo}/commit/${commit}\u0001"},
             refused("revision_url_must_name_a_commit")),
        call("open-url-no-scheme", "opener", "stream.open", {"proof_revision_url": 'example.org/a/b/commit/${commit}'},
             refused("revision_url_must_name_a_commit")),
        call("open-url-no-path", "opener", "stream.open", {"proof_revision_url": 'https://example.org/commit/${commit}'},
             refused("revision_url_must_name_a_commit")),
        call("open-url-hash-short", "opener", "stream.open", {"proof_revision_url": '${repo}#abc1234'},
             refused("revision_url_must_name_a_commit")),
        call("open-url-at-after-hash", "opener", "stream.open",      # a revision URL (by its @), of another repository
             {"proof_revision_url": "${repo}#${commit}@${commit}"}, refused("repository_must_match_the_engine")),
        call("open-url-tree-without-package", "opener", "stream.open", {"proof_revision_url": '${repo}/tree/${commit}'},
             refused("revision_url_must_name_a_commit")),
        call("open-url-tree-trailing-slash", "opener", "stream.open", {"proof_revision_url": '${repo}/tree/${commit}/'},
             refused("revision_url_must_name_a_commit")),
        call("open-url-tree-empty-segment", "opener", "stream.open", {"proof_revision_url": '${repo}/tree/${commit}/examples//log'},
             refused("revision_url_must_name_a_commit")),
        call("open-url-tree-dot-segment", "opener", "stream.open", {"proof_revision_url": '${repo}/tree/${commit}/examples/../tasks'},
             refused("revision_url_must_name_a_commit")),
        call("open-url-tree-dot", "opener", "stream.open", {"proof_revision_url": '${repo}/tree/${commit}/./log'},
             refused("revision_url_must_name_a_commit")),
        call("open-url-tree-bad-character", "opener", "stream.open", {"proof_revision_url": '${repo}/tree/${commit}/examples/log~1'},
             refused("revision_url_must_name_a_commit")),
        call("open-url-tree-short-commit", "opener", "stream.open", {"proof_revision_url": '${repo}/tree/abc1234/x'},
             refused("revision_url_must_name_a_commit")),
        call("open-url-commit-with-package", "opener", "stream.open", {"proof_revision_url": '${repo}/commit/${commit}/examples/log'},
             refused("revision_url_must_name_a_commit")),
        call("open-url-too-long", "opener", "stream.open", {"proof_revision_url": "${repo}/commit/${commit}#" + "x" * 2048},
             refused("revision_url_must_name_a_commit")),
        call("open-unknown-revision", "opener", "stream.open", {"proof_revision_url": "${repo}/commit/" + NO_COMMIT},
             refused("revision_must_be_installed")),
        call("open-unknown-package", "opener", "stream.open",
             {"proof_revision_url": "${repo}/tree/${commit}/examples/nothing"}, refused("revision_must_be_installed")),
        call("open-another-repository", "opener", "stream.open",
             {"proof_revision_url": "https://example.org/another/repository/commit/${commit}"},
             refused("repository_must_match_the_engine")),
        call("open-another-repository-package", "opener", "stream.open",
             {"proof_revision_url": "https://example.org/another/repository/tree/${commit}/examples/log"},
             refused("repository_must_match_the_engine"), proof="log"),
        call("open-the-repository-spelled-with-git", "opener", "stream.open",
             {"proof_revision_url": "${repo}.git#${commit}"},
             accepted(0, {"event": "stream.opened", "stream_id": "$uuid:s3", "actor_id": "$opener", "meta": None,
                          "proof_revision_url": "${repo}.git#${commit}"}, "$hex64:e0")),
        call("open-the-repository-at", "opener", "stream.open", {"proof_revision_url": "${repo}@${commit}"},
             accepted(0, {"event": "stream.opened", "stream_id": "$uuid:s4", "actor_id": "$opener", "meta": None,
                          "proof_revision_url": "${repo}@${commit}"}, "$hex64:f0")),
        call("unknown-stream-close", "opener", "stream.close", {"stream_id": NOWHERE}, refused("stream_must_exist")),
        call("unknown-stream-layer-command", "opener", "task.open", {"stream_id": NOWHERE, "task_id": NOWHERE},
             refused("stream_must_exist")),
        call("open-on-not-the-interface", "opener", "stream.open", {"proof_revision_url": "$notiface_url"},
             refused("engine_must_implement_the_interface"), local_only=True),
        call("open-on-not-the-interface-again", "other", "stream.open", {"proof_revision_url": "$notiface_url"},
             refused("engine_must_implement_the_interface"), local_only=True),
        call("open-on-a-broken-engine", "opener", "stream.open", {"proof_revision_url": "$broken_url"},
             err("unavailable", retry=True, incident="$uuid"), local_only=True),
        call("open-on-a-broken-engine-retried", "opener", "stream.open",
             {"proof_revision_url": "$broken_url", "idempotency_key": "broken-${run}"},
             err("unavailable", retry=True, incident="$uuid"), local_only=True),
        call("describe-a-broken-engine", "outsider", "revision.describe", {"revision": "$broken"},
             err("unavailable", retry=True, incident="$uuid"), local_only=True),
        call("served-after-broken", "opener", "stream.head", {"stream_id": s},
             ok({"stream_id": s, "length": 1, "chain": "$c0"})),
    ]


HOST_THEMES = [("auth", auth), ("parse", parse), ("reads", reads), ("paging", paging), ("idempotency", idempotency),
               ("actor", actor), ("discovery", discovery), ("host", host_commands), ("errors", errors)]


def line(x):
    return json.dumps(x, ensure_ascii=False, separators=(",", ":"))


def render():
    out = {}
    themes = [(p, lambda p=p: proof_theme(p)) for p in PROOFS] + HOST_THEMES
    for theme, make in themes:
        cases = make()
        ids = [c["id"] for c in cases]
        assert len(set(ids)) == len(ids), "%s: repeated case ids" % theme
        out[theme + ".jsonl"] = "".join(line(dict(c, id="%s/%s" % (theme, c["id"]))) + "\n" for c in cases)
    return out


def main(argv):
    check = argv[1:] == ["--check"]
    files = render()
    stale = []
    for name, text in files.items():
        path = os.path.join(CASES, name)
        old = open(path, encoding="utf-8").read() if os.path.exists(path) else None
        if old != text:
            stale.append(name)
            if not check:
                os.makedirs(CASES, exist_ok=True)
                with open(path, "w", encoding="utf-8") as f:
                    f.write(text)
    extra = sorted(set(os.listdir(CASES)) - set(files)) if os.path.isdir(CASES) else []
    if check:
        if stale or extra:
            print("conformance cases are stale (%s): run python3 conformance/make_cases.py"
                  % " ".join(stale + extra), file=sys.stderr)
            return 1
        print("conformance cases: as make_cases.py writes them")
        return 0
    for name in extra:
        os.remove(os.path.join(CASES, name))
    print("conformance cases: %d files, %d cases" % (len(files), sum(t.count("\n") for t in files.values())))
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
