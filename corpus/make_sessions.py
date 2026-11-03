#!/usr/bin/env python3
# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Write the corpus's input sessions (`sessions/*.in.jsonl`), deterministically. `corpus/record` then runs each through
a fresh engine and seals the outputs; `corpus/replay` checks them byte for byte.

Each session's prefix names its engine: `core-*` the core's (`.lake/build/bin/core-engine`), `log-*`, `principals-*`,
`tasks-*` and `work-*` the examples' (`examples/<name>`), `tower-*` the three-level tower's (`tests/tower`). The `core-*`
sessions are also the stream interface's (`host/provenstream/interface/`, byte-identical copies): every engine must
answer them as the core does.

    python3 corpus/make_sessions.py           write every session
"""
import json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
C40 = "4f1c2a9e0b7d3c6a5f8e1d2c3b4a59687f6e5d4c"
C64 = "9e107d9d372bb6826bd81d3542a419d6c1f2e3d4b5a697887766554433221100"
REPO = "https://git.example.org/acme/notebook"
URL = REPO + "/commit/" + C40                                    # the root package of a commit
TREE = REPO + "/tree/" + C40 + "/examples/tasks"                 # another package of the same commit
ANN, BEN, CY, DEE, EVE = ("a0000000-0000-4000-8000-000000000001", "b0000000-0000-4000-8000-000000000002",
                          "c0000000-0000-4000-8000-000000000003", "d0000000-0000-4000-8000-000000000004",
                          "e0000000-0000-4000-8000-000000000005")
S1, S2, S3, S4, S5 = ("50000000-0000-7000-8000-000000000001", "50000000-0000-7000-8000-000000000002",
                      "50000000-0000-7000-8000-000000000003", "50000000-0000-7000-8000-000000000004",
                      "50000000-0000-7000-8000-000000000005")
W1, W2, W3, W4, W5, W9 = ("70000000-0000-7000-8000-000000000001", "70000000-0000-7000-8000-000000000002",
                          "70000000-0000-7000-8000-000000000003", "70000000-0000-7000-8000-000000000004",
                          "70000000-0000-7000-8000-000000000005", "70000000-0000-7000-8000-000000000009")


def line(x):
    return json.dumps(x, ensure_ascii=False, separators=(",", ":"))


def req(actor, command, fresh=()):
    return {"actor_id": actor, "command": command, "fresh": list(fresh)}


def open_(actor, stream, url=URL, meta=None):
    c = {"command": "stream.open", "proof_revision_url": url}
    if meta is not None:
        c["meta"] = meta
    return req(actor, c, [stream])


def close(actor, stream, meta=None):
    c = {"command": "stream.close", "stream_id": stream}
    if meta is not None:
        c["meta"] = meta
    return req(actor, c)


def cmd(actor, name, stream, **kv):
    return req(actor, dict({"command": name, "stream_id": stream}, **kv))


def read(stream):
    return {"query": "stream", "stream_id": stream}


SCHEMA = {"query": "schema"}


def core_rules():
    """Every core rule refusing, in the order the rules are tried, and both commands accepted; reads and the schema."""
    return [
        close(ANN, S1),                                                          # stream_must_exist
        open_(ANN, S1, url=REPO + "/commit/4f1c2a9"),                           # revision_url_must_name_a_commit: 7 hex
        open_(ANN, S1, url=REPO + "/commit/" + C40.upper()),                     # ...: not lowercase
        open_(ANN, S1, url=REPO + "/tree/" + C40),                               # ...: a tree with no package
        open_(ANN, S1, url=REPO + "/tree/" + C40 + "/"),                         # ...: an empty package
        open_(ANN, S1, url=REPO + "/tree/" + C40 + "/examples//tasks"),          # ...: an empty segment
        open_(ANN, S1, url=REPO + "/tree/" + C40 + "/examples/../tasks"),        # ...: a `..` segment
        open_(ANN, S1, url=REPO + "/tree/" + C40 + "/./tasks"),                  # ...: a `.` segment
        open_(ANN, S1, url=REPO + "/tree/" + C40 + "/examples/tasks~1"),        # ...: a character not in [A-Za-z0-9._-]
        open_(ANN, S1, url="https://git.example.org/tree/" + C40 + "/tasks"),    # ...: no repository path
        open_(ANN, S1, url="git.example.org/acme/notebook/commit/" + C40),       # ...: no scheme
        open_(ANN, S1, url=REPO + "/commit/" + C40 + " "),                       # ...: whitespace
        open_(ANN, S1, meta="the first stream"),                                 # accepted
        open_(DEE, S1),                                                          # stream_id_must_be_new
        open_(DEE, S1, url=REPO + "/commit/4f1c2a9"),                            # stream_id_must_be_new: tried first
        open_(ANN, S2) | {"fresh": []},                                          # fresh_ids_must_match_the_command
        open_(ANN, S2) | {"fresh": [S2, S3]},                                    # fresh_ids_must_match_the_command
        close(ANN, S1) | {"fresh": [S2]},                                        # fresh_ids_must_match_the_command
        open_(BEN, S2, url=TREE),                                                # accepted: a package of the commit
        open_(CY, S3, url="https://git.example.org/acme/notebook.git#" + C64),   # accepted: `#`, a SHA-256 commit
        open_(DEE, S4, url="ssh+git://git.example.org/acme/notebook@" + C40),    # accepted: `@`
        open_(EVE, S5, url=REPO + "/tree/" + C40 + "/proofs/v1.2_rc-3/Main"),    # accepted: every segment character
        read(S1),
        close(BEN, S1),                                                          # only_opener_can_close
        close(CY, S1, meta="closing someone else's stream"),                     # only_opener_can_close
        close(ANN, S2),                                                          # only_opener_can_close: S2 is BEN's
        close(ANN, S1, meta="done"),                                             # accepted
        close(ANN, S1),                                                          # stream_must_be_open
        close(BEN, S1),                                                          # stream_must_be_open: tried first
        open_(EVE, S1),                                                          # stream_id_must_be_new: never reopened
        close(BEN, S2),                                                          # accepted: by its opener
        read(S1),
        read(S2),
        read(S3),
        read("50000000-0000-7000-8000-000000000006"),                            # stream_must_exist
        SCHEMA,
    ]


def malformed(cmd_name):
    """Lines no engine decides: not JSON, not a request, not of its form; and the cache messages' malformed forms."""
    return [
        "not json",
        "[1,2]",
        line({"actor_id": ANN, "command": {"command": cmd_name, "stream_id": S1}}),                     # no fresh
        line({"actor_id": ANN, "command": {"command": "nope", "stream_id": S1}, "fresh": []}),
        line({"actor_id": "ANN", "command": {"command": "stream.close", "stream_id": S1}, "fresh": []}),
        line({"actor_id": ANN.upper(), "command": {"command": "stream.close", "stream_id": S1}, "fresh": []}),
        line({"actor_id": 1, "command": {"command": "stream.close", "stream_id": S1}, "fresh": []}),
        line({"command": {"command": "stream.close", "stream_id": S1}, "fresh": []}),                   # no actor_id
        line({"caller": {"principal": ANN}, "command": {"command": "stream.close", "stream_id": S1}, "fresh": []}),
        line({"actor_id": ANN, "command": {"command": "stream.close", "stream": S1}, "fresh": []}),     # `stream`
        line({"actor_id": ANN, "command": {"command": "stream.close"}, "fresh": []}),
        line({"actor_id": ANN, "command": {"command": "stream.close", "stream_id": S1, "actor_id": BEN},
              "fresh": []}),
        line({"actor_id": ANN, "command": {"command": "stream.close", "stream_id": S1, "meta": "a\u0001b"},
              "fresh": []}),
        line({"actor_id": ANN, "command": {"command": "stream.close", "stream_id": S1, "meta": 7}, "fresh": []}),
        line({"actor_id": ANN, "command": {"command": "stream.close", "stream_id": S1, "meta": "x" * 4097},
              "fresh": []}),
        line({"actor_id": ANN, "command": {"command": "stream.open", "proof_revision_url": URL, "stream_id": S1},
              "fresh": [S1]}),                                                                          # minted
        line({"actor_id": ANN, "command": {"command": "stream.open"}, "fresh": [S1]}),
        line({"actor_id": ANN, "command": {"command": "stream.open", "proof_revision_url": 7}, "fresh": [S1]}),
        line({"actor_id": ANN, "command": {"command": "stream.open", "proof_revision_url": URL}, "fresh": ["s1"]}),
        line({"actor_id": ANN, "command": {"command": "stream.open", "proof_revision_url": URL,
              "actor_kind": "person"}, "fresh": [S1]}),                                                 # no kinds
        line({"actor_id": ANN, "command": "stream.close", "fresh": []}),
        line({"sync": {"stream_id": S1}}),
        line({"load": {"stream_id": S1, "k": 0}}),
        line({"sync": {"stream": S1, "from": 0, "rows": []}}),                                      # `stream`
        line({"query": "stream"}),
        line({"query": "nothing"}),
        "",
        "   ",
        line({"actor_id": ANN, "command": {"command": "stream.close", "stream_id": S1}, "fresh": [], "extra": 1}),
    ]


def write(name, items):
    path = os.path.join(HERE, "sessions", name + ".in.jsonl")
    with open(path, "w", encoding="utf-8") as f:
        for it in items:
            f.write((it if isinstance(it, str) else line(it)) + "\n")
    print("wrote", os.path.relpath(path, HERE))


def engine_events(engine, requests):
    """The events a fresh engine accepts for these requests, in order (to build the cache session's stored rows)."""
    import subprocess
    out = subprocess.run([engine], input="".join(line(r) + "\n" for r in requests), capture_output=True, text=True,
                         check=True).stdout.splitlines()[1:]
    rows = []
    for r, o in zip(requests, out):
        a = json.loads(o)
        if a.get("accept"):
            rows.append({"request": r, "event": a["event"]})
    return rows


def core_cache(engine):
    """sync, snapshot, drop, check and every outcome of each, on the core's engine."""
    rows = engine_events(engine, [open_(ANN, S1), close(ANN, S1, meta="done")])
    rows2 = engine_events(engine, [open_(BEN, S2, url=TREE), close(BEN, S2)])
    assert len(rows) == 2 and len(rows2) == 2, (rows, rows2)
    # the close's event with another actor: not the translation of its request
    forged = dict(rows[1], event=dict(rows[1]["event"], actor_id=BEN))
    # a close by someone other than the opener, request and event agreeing: translated, but not Valid
    by_ben = {"request": dict(rows[1]["request"], actor_id=BEN), "event": dict(rows[1]["event"], actor_id=BEN)}
    return [
        read(S1),                                                     # stream_must_exist: nothing held
        {"sync": {"stream_id": S1, "from": 0, "rows": []}},              # an empty sync creates nothing
        read(S1),
        {"sync": {"stream_id": S1, "from": 1, "rows": rows[:1]}},        # out_of_sync
        {"sync": {"stream_id": S1, "from": 0, "rows": [rows[0], forged]}},  # refused: not the translation
        {"sync": {"stream_id": S1, "from": 0, "rows": [rows[1]]}},       # refused: stream_must_exist
        {"sync": {"stream_id": S1, "from": 0, "rows": [rows[0], by_ben]}},  # refused: only_opener_can_close
        {"sync": {"stream_id": S1, "from": 0, "rows": rows[:1]}},        # synced
        {"snapshot": S1},
        read(S1),
        open_(BEN, S1),                                               # decided at 1: stream_id_must_be_new
        close(BEN, S1),                                               # decided at 1: only_opener_can_close
        {"sync": {"stream_id": S2, "from": 0, "rows": rows2[:1]}},       # synced
        {"sync": {"stream_id": S2, "from": 1, "rows": rows2[1:]}},       # synced: from where the engine is
        {"sync": {"stream_id": S2, "from": 1, "rows": rows2[1:]}},       # out_of_sync: the engine is at 2
        close(BEN, S2),                                               # stream_must_be_open at 2
        {"drop": S1},
        read(S1),
        {"check": {"stream_id": S1, "rows": rows}},                      # the audit path
        {"check": {"stream_id": S1, "rows": [rows[1]]}},                 # refused: stream_must_exist
        {"check": {"stream_id": S1, "rows": [rows[0], by_ben]}},         # refused: only_opener_can_close
        {"check": {"stream_id": S1, "rows": [rows[0], forged]}},         # refused: not the translation
        {"check": {"stream_id": S2, "rows": rows}},                      # rows of another stream
        {"sync": {"stream_id": S1, "from": 0, "rows": rows}},
        close(ANN, S1),                                               # stream_must_be_open at 2
        read(S1),
    ]


def log_rules():
    """The log layer: its one rule refusing, the core's admission on its events, and log.append accepted."""
    def append(actor, stream, text, **kv):
        return cmd(actor, "log.append", stream, text=text, **kv)
    return [
        append(ANN, S1, "before the stream"),                        # stream_must_exist (admission)
        open_(ANN, S1, url=REPO + "/tree/" + C40 + "/examples/log", meta="a notebook"),
        append(ANN, S1, "first entry", meta="2026-10-30"),           # accepted
        append(BEN, S1, "an entry by someone else"),                 # only_opener_can_append
        append(ANN, S1, "Grüße, 世界: \"quoted\" and \\ backslash"),  # accepted: any text
        append(ANN, S1, ""),                                         # accepted: an empty text
        open_(BEN, S2, url=REPO + "/tree/" + C40 + "/examples/log"),
        append(ANN, S2, "in BEN's notebook"),                        # only_opener_can_append: S2 is BEN's
        append(BEN, S2, "BEN's own entry"),                          # accepted
        append(ANN, S1, "line\nbreak\ttab"),                         # accepted: a text may hold control characters
        append(ANN, S1, "a\u0000b"),                                  # malformed: only U+0000 is refused in a text
        read(S1),
        close(BEN, S1),                                              # only_opener_can_close
        close(ANN, S1),                                              # accepted
        append(ANN, S1, "after the close"),                          # stream_must_be_open (admission)
        read(S1),
        SCHEMA,
    ]


def principals_rules():
    """The principals layer: every rule refusing, in order where two fail, and every command accepted."""
    def invite(actor, stream, p):
        return cmd(actor, "principal.invite", stream, principal_id=p)

    def promote(actor, stream, p):
        return cmd(actor, "principal.promote", stream, principal_id=p)

    def summon(actor, stream, p, **kv):
        return cmd(actor, "principal.summon", stream, principal_id=p, **kv)
    purl = REPO + "/tree/" + C40 + "/examples/principals"
    return [
        invite(ANN, S1, BEN),                                        # stream_must_exist (admission)
        open_(ANN, S1, url=purl),                                    # ANN, the opener: the first admin
        invite(BEN, S1, CY),                                         # only_admins_can_invite: BEN is nobody here
        invite(ANN, S1, ANN),                                        # principal_must_be_new: the opener
        invite(ANN, S1, BEN),                                        # accepted: BEN, a person
        invite(ANN, S1, BEN),                                        # principal_must_be_new: invited
        invite(BEN, S1, DEE),                                        # only_admins_can_invite: invited, not promoted
        summon(BEN, S1, CY),                                         # only_admins_can_summon
        promote(BEN, S1, BEN),                                       # only_admins_can_promote
        summon(ANN, S1, CY, meta="the build agent"),                 # accepted: CY, an agent
        summon(ANN, S1, BEN),                                        # principal_must_be_new: invited
        invite(ANN, S1, CY),                                         # principal_must_be_new: summoned
        summon(ANN, S1, CY),                                         # principal_must_be_new: summoned
        summon(ANN, S1, ANN),                                        # principal_must_be_new: the opener
        promote(ANN, S1, CY),                                        # principal_must_be_invited: an agent
        promote(ANN, S1, DEE),                                       # principal_must_be_invited: never declared
        promote(ANN, S1, ANN),                                       # principal_must_be_invited: the opener
        promote(ANN, S1, BEN),                                       # accepted: BEN, an admin
        promote(ANN, S1, BEN),                                       # principal_is_promoted_once
        invite(BEN, S1, DEE),                                        # accepted: by a promoted admin
        promote(BEN, S1, DEE),                                       # accepted: by a promoted admin
        summon(DEE, S1, EVE),                                        # accepted
        promote(CY, S1, DEE),                                        # only_admins_can_promote: tried first
        invite(CY, S1, EVE),                                         # only_admins_can_invite: tried first
        promote(DEE, S1, EVE),                                       # principal_must_be_invited: an agent
        open_(BEN, S2, url=purl),
        invite(ANN, S2, CY),                                         # only_admins_can_invite: roles are per stream
        summon(BEN, S2, ANN),                                        # accepted: ANN, an agent in S2
        read(S1),
        close(BEN, S1),                                              # only_opener_can_close: an admin is not the opener
        close(ANN, S1),                                              # accepted
        invite(ANN, S1, EVE),                                        # stream_must_be_open (admission)
        promote(BEN, S1, DEE),                                       # stream_must_be_open: tried first
        read(S1),
        read(S2),
        SCHEMA,
    ]


def task(actor, name, stream, k, **kv):
    return cmd(actor, name, stream, task_id=k, **kv)


def tasks_commands(stream):
    """Task and review commands on `stream`: `t(actor, name, task_id, **params)`."""
    return lambda actor, name, k, **kv: task(actor, name, stream, k, **kv)


def tasks_rules():
    """The tasks layer: every layer rule refusing, in order where two fail, the core's admission on its events, and
    every command accepted. A parent is named by its own task_id, a task of the same stream (`parent_task_must_exist`:
    not an unknown id, not the stream's, not the task's own, not a task of another stream)."""
    t = tasks_commands(S1)
    t2 = tasks_commands(S2)
    return [
        t(ANN, "task.open", W1),                                     # stream_must_exist (admission)
        open_(ANN, S1, url=TREE),                                    # at 0
        t(BEN, "task.open", W1),                                     # only_opener_can_open_tasks
        t(ANN, "task.open", W1, meta="write the spec"),              # accepted, at 1
        t(ANN, "task.open", W1),                                     # task_id_must_be_new
        t(BEN, "task.open", W1),                                     # only_opener_can_open_tasks: tried first
        t(ANN, "task.open", W2, parent_task_id=W9),                  # parent_task_must_exist: no task W9
        t(BEN, "task.open", W2, parent_task_id=W9),                  # only_opener_can_open_tasks: tried first
        t(ANN, "task.open", W2, parent_task_id=S1),                  # parent_task_must_exist: the stream is no task
        t(ANN, "task.open", W2, parent_task_id=W2),                  # parent_task_must_exist: not its own parent
        t(ANN, "task.open", W1, parent_task_id=W9),                  # task_id_must_be_new: tried first
        t(ANN, "task.open", W2, parent_task_id=W1, meta="a child of W1"),  # accepted: a child task, at 2
        t(ANN, "task.open", W3, parent_task_id=None),                # accepted: no parent, at 3
        t(ANN, "task.open", W4),                                     # accepted, at 4
        t(BEN, "task.assign", W1, assignee_id=CY),                   # only_opener_can_assign
        t(ANN, "task.assign", W9, assignee_id=CY),                   # task_must_exist
        t(BEN, "task.assign", W9, assignee_id=CY),                   # only_opener_can_assign: tried first
        t(ANN, "task.assign", W1, assignee_id=CY, meta="CY writes it"),  # accepted, at 5
        t(ANN, "task.assign", W1, assignee_id=DEE),                  # task_is_assigned_once
        t(ANN, "task.assign", W1, assignee_id=CY),                   # task_is_assigned_once: even to the same one
        t(ANN, "task.assign", W2, assignee_id=ANN),                  # accepted: the opener to itself, at 6
        t(ANN, "task.assign", W4, assignee_id=BEN),                  # accepted, at 7
        t(CY, "task.complete", W9),                                  # task_must_exist
        t(CY, "task.complete", W3),                                  # only_assignee_can_finish: unassigned
        t(ANN, "task.complete", W3),                                 # only_assignee_can_finish: the opener, unassigned
        t(DEE, "task.complete", W1),                                 # only_assignee_can_finish
        t(ANN, "task.complete", W1),                                 # only_assignee_can_finish: the opener
        t(BEN, "task.complete", W1),                                 # only_assignee_can_finish: another's assignee
        t(CY, "task.complete", W1, meta="written"),                  # accepted, at 8
        t(CY, "task.complete", W1),                                  # task_is_completed_once
        t(ANN, "task.complete", W2),                                 # accepted: the opener, assigned to itself, at 9
        t(ANN, "task.open", W9, parent_task_id=W1),                  # accepted: a child of a completed task, at 10
        open_(ANN, S2, url=TREE),                                    # another stream, at 0 of S2
        t2(ANN, "task.open", W5),                                    # accepted, at 1 of S2
        t(ANN, "task.open", W5, parent_task_id=W5),                  # parent_task_must_exist: W5 is S2's, not S1's
        t2(ANN, "task.open", W3, parent_task_id=W1),                 # parent_task_must_exist: W1 is S1's, not S2's
        t2(ANN, "task.open", W4, parent_task_id=W5),                 # accepted: a child of W5, at 2 of S2
        read(S2),
        read(S1),
        close(BEN, S1),                                              # only_opener_can_close
        close(ANN, S1),                                              # accepted: W3 and W4 not completed
        t(ANN, "task.open", W9),                                     # stream_must_be_open (admission)
        t(BEN, "task.complete", W4),                                 # stream_must_be_open
        read(S1),
        SCHEMA,
    ]


def tasks_malformed():
    """The core's malformed lines on a task command, then the task commands' own."""
    t = tasks_commands(S1)
    return malformed("task.open") + [line(x) for x in [
        t(ANN, "task.open", W2, parent_task_id=1),                   # a parent is its task_id, not a seq
        t(ANN, "task.open", W2, parent_task_id="1"),                 # not a UUID
        t(ANN, "task.open", W2, parent_task_id="W1"),
        t(ANN, "task.open", W2, parent_task_id="A" + W1[1:]),            # not canonical: uppercase
        t(ANN, "task.open", W2, parent_task_id=[W1]),
        t(ANN, "task.open", "W2"),
        cmd(ANN, "task.open", S1),                                   # no task_id
        t(ANN, "task.assign", W1),                                   # no assignee_id
        t(ANN, "task.assign", W1, assignee_id="CY"),
        t(ANN, "task.assign", W1, principal=CY),                     # not the name of the field
        t(ANN, "task.complete", W1, assignee_id=CY),
        t(ANN, "task.done", W1),                                     # not a command (now task.complete)
        t(ANN, "task.open", W2, ref=1),                              # not the name of the field (now parent_task_id)
    ]]


def work_commands(stream):
    """Work commands on `stream`: `w(actor, name, work_id, **params)`."""
    return lambda actor, name, k, **kv: cmd(actor, name, stream, work_id=k, **kv)


def work_rules():
    """The work layer: every layer rule refusing, in order where two fail, the core's admission on its events, and
    every command accepted. The opener creates and assigns (to itself too); the assignee asks preparers other than
    itself, each once, and decides once; the asked reply once; nothing about a decided item is accepted."""
    wurl = REPO + "/tree/" + C40 + "/examples/work"
    w = work_commands(S1)
    return [
        w(ANN, "work.create", W1),                                   # stream_must_exist (admission)
        open_(ANN, S1, url=wurl),                                    # at 0
        w(BEN, "work.create", W1),                                   # only_opener_can_create
        w(ANN, "work.create", W1, meta="write the brief"),           # accepted, at 1
        w(ANN, "work.create", W1),                                   # work_id_must_be_new
        w(BEN, "work.create", W1),                                   # only_opener_can_create: tried first
        w(BEN, "work.assign", W1, assignee_id=BEN),                  # only_opener_can_assign
        w(ANN, "work.assign", W9, assignee_id=BEN),                  # work_must_exist
        w(BEN, "work.ask", W1, preparer_id=CY),                      # only_assignee_can_ask: unassigned
        w(BEN, "work.complete", W1),                                 # only_assignee_can_decide: unassigned
        w(ANN, "work.assign", W1, assignee_id=BEN, meta="BEN runs it"),  # accepted, at 2
        w(ANN, "work.assign", W1, assignee_id=CY),                   # work_is_assigned_once
        w(ANN, "work.assign", W1, assignee_id=BEN),                  # work_is_assigned_once: even to the same one
        w(ANN, "work.ask", W1, preparer_id=CY),                      # only_assignee_can_ask: the opener
        w(BEN, "work.ask", W9, preparer_id=CY),                      # work_must_exist
        w(BEN, "work.ask", W1, preparer_id=BEN),                     # preparer_must_not_be_the_assignee
        w(CY, "work.reply", W1),                                     # only_asked_preparers_can_reply: not asked
        w(BEN, "work.ask", W1, preparer_id=CY, meta="please prepare"),  # accepted, at 3
        w(BEN, "work.ask", W1, preparer_id=CY),                      # preparer_is_asked_once
        w(BEN, "work.ask", W1, preparer_id=DEE),                     # accepted: any number of preparers, at 4
        w(BEN, "work.ask", W1, preparer_id=ANN),                     # accepted: the opener may prepare, at 5
        w(DEE, "work.reply", W9),                                    # work_must_exist
        w(BEN, "work.reply", W1),                                    # only_asked_preparers_can_reply: the assignee
        w(CY, "work.reply", W1, meta="https://example.org/preparations/cy"),  # accepted, at 6
        w(CY, "work.reply", W1),                                     # preparer_replies_once
        w(CY, "work.complete", W1),                                  # only_assignee_can_decide: a preparer
        w(ANN, "work.cancel", W1),                                   # only_assignee_can_decide: the opener
        w(BEN, "work.complete", W9),                                 # work_must_exist
        w(BEN, "work.cancel", W9),                                   # work_must_exist
        w(BEN, "work.complete", W1, meta="done"),                    # accepted, at 7
        w(BEN, "work.complete", W1),                                 # work_is_decided_once
        w(BEN, "work.cancel", W1),                                   # work_is_decided_once
        w(BEN, "work.ask", W1, preparer_id=EVE),                     # work_must_be_undecided
        w(DEE, "work.reply", W1),                                    # work_must_be_undecided: asked, never replied
        w(ANN, "work.create", W2),                                   # accepted, at 8
        w(ANN, "work.assign", W2, assignee_id=ANN),                  # accepted: the opener to itself, at 9
        w(ANN, "work.cancel", W2, meta="won't be done"),             # accepted: cancelled, nobody asked, at 10
        w(ANN, "work.complete", W2),                                 # work_is_decided_once
        w(ANN, "work.create", W3),                                   # accepted, at 11
        w(ANN, "work.assign", W3, assignee_id=BEN),                  # accepted, at 12
        w(BEN, "work.complete", W3),                                 # accepted: completed, no preparer, at 13
        read(S1),
        close(BEN, S1),                                              # only_opener_can_close
        close(ANN, S1),                                              # accepted, at 14
        w(ANN, "work.create", W4),                                   # stream_must_be_open (admission)
        read(S1),
        SCHEMA,
    ]


def work_malformed():
    """The core's malformed lines on a work command, then the work commands' own."""
    w = work_commands(S1)
    return malformed("work.create") + [line(x) for x in [
        w(ANN, "work.create", "W1"),                                 # not a UUID
        w(ANN, "work.create", "A" + W1[1:]),                         # not canonical: uppercase
        cmd(ANN, "work.create", S1),                                 # no work_id
        w(ANN, "work.assign", W1),                                   # no assignee_id
        w(ANN, "work.assign", W1, assignee_id="BEN"),
        w(BEN, "work.ask", W1),                                      # no preparer_id
        w(BEN, "work.ask", W1, preparer_id=5),
        w(BEN, "work.ask", W1, principal=CY),                        # not the name of the field
        w(CY, "work.reply", W1, preparer_id=CY),                     # not a field of reply
        w(BEN, "work.complete", W1, assignee_id=BEN),                # not a field of complete
        w(BEN, "work.review", W1, preparer_id=CY),                   # not a command
        cmd(ANN, "task.open", S1, task_id=W1),                       # another layer's command
    ]]


def tower_rules():
    """The tower (reviews on tasks on the core): every rule of the review layer refusing, its guard on the core's
    stream.close, the tasks layer's and the core's rules still judging at the top, and every command accepted."""
    t = tasks_commands(S1)
    turl = REPO + "/tree/" + C40 + "/tests/tower"
    return [
        t(ANN, "review.approve", W1),                                # stream_must_exist (admission)
        open_(ANN, S1, url=turl),                                    # at 0
        t(ANN, "task.open", W1),                                     # at 1
        t(ANN, "task.open", W2, parent_task_id=W1),                  # at 2: a child of W1
        t(ANN, "task.open", W4, parent_task_id=W9),                  # parent_task_must_exist (tasks, below)
        t(BEN, "task.open", W4, parent_task_id=W9),                  # only_opener_can_open_tasks: tried first
        t(ANN, "task.open", W3),                                     # at 3
        t(ANN, "task.assign", W1, assignee_id=CY),                   # at 4
        t(ANN, "task.assign", W2, assignee_id=DEE),                  # at 5
        t(ANN, "review.approve", W1),                                # task_must_be_completed: open, not completed
        t(BEN, "review.approve", W1),                                # only_opener_can_approve
        t(ANN, "review.approve", W9),                                # task_must_be_completed: no such task
        t(CY, "task.complete", W1),                                  # accepted, at 6
        t(CY, "review.approve", W1),                                 # only_opener_can_approve: the assignee
        t(BEN, "review.approve", W1),                                # only_opener_can_approve
        close(ANN, S1),                                              # completed_tasks_must_be_approved_before_close
        close(BEN, S1),                                              # only_opener_can_close: the core's rule first
        t(ANN, "review.approve", W1, meta="looks right"),            # accepted, at 7
        t(ANN, "review.approve", W1),                                # task_is_approved_once
        t(BEN, "review.approve", W1),                                # only_opener_can_approve: tried first
        t(ANN, "review.approve", W3),                                # task_must_be_completed: open, unassigned
        t(BEN, "task.open", W4),                                     # only_opener_can_open_tasks (tasks, below)
        t(CY, "task.complete", W3),                                  # only_assignee_can_finish (tasks, below)
        open_(ANN, S2, url=turl),                                    # another stream, at 0 of S2
        cmd(ANN, "task.open", S2, task_id=W5),                       # accepted, at 1 of S2
        t(ANN, "task.open", W4, parent_task_id=W5),                  # parent_task_must_exist: W5 is S2's, not S1's
        t(DEE, "task.complete", W2),                                 # accepted, at 8
        close(ANN, S1),                                              # completed_tasks_must_be_approved_before_close
        read(S1),
        t(ANN, "review.approve", W2),                                # accepted, at 9
        close(ANN, S1),                                              # accepted: W3 is open, not completed
        t(ANN, "review.approve", W2),                                # stream_must_be_open (admission)
        close(ANN, S1),                                              # stream_must_be_open: before the guard
        t(DEE, "task.complete", W3),                                 # stream_must_be_open
        read(S1),
        SCHEMA,
    ]


def main():
    root = os.path.dirname(HERE)
    write("core-rules", core_rules())
    write("core-cache", core_cache(os.path.join(root, ".lake", "build", "bin", "core-engine")))
    write("core-malformed", malformed("stream.close"))
    write("log-rules", log_rules())
    write("principals-rules", principals_rules())
    write("tasks-rules", tasks_rules())
    write("tasks-malformed", tasks_malformed())
    write("work-rules", work_rules())
    write("work-malformed", work_malformed())
    write("tower-rules", tower_rules())


if __name__ == "__main__":
    main()
