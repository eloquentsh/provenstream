# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Model honesty: the worked story of EmailTriageAndReply/Examples.lean, parsed from the Lean file, run through the
Python model (mailbox_model.py) and through the compiled engine. The model must give every answer the Lean story
expects (`#guard answersOk` holds them at build time), and so must the engine. The story is read from the file, so a
change to it is a change to this test.
"""
from __future__ import annotations
import os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(REPO, "host"))
sys.path.insert(0, HERE)

import pytest
from provenstream.engine import Engine
import mailbox_model as M

PACKAGE = os.path.join(REPO, "examples", "email-triage-and-reply")
EXAMPLES = os.path.join(PACKAGE, "EmailTriageAndReply", "Examples.lean")
ENGINE = os.environ.get("MAILBOX_ENGINE") or os.path.join(PACKAGE, ".lake", "build", "bin", "email-triage-and-reply-engine")

# (helper, constructor) -> (command, the fields its positional arguments fill, in order; `meta` is always last)
CONSTRUCTORS = {
    ("pr", "invite"): ("principal.invite", ["stream_id", "principal_id"]),
    ("pr", "summon"): ("principal.summon", ["stream_id", "principal_id"]),
    ("pr", "delegate"): ("principal.delegate", ["stream_id", "delegate_id"]),
    ("em", "create"): ("email.create", ["stream_id", "email_id", "in_reply_to_eml_url"]),
    ("em", "solicit"): ("email.solicit", ["stream_id", "email_id", "preparer_id"]),
    ("em", "prepare"): ("email.prepare", ["stream_id", "email_id", "preparation_url"]),
    ("em", "draft"): ("email.draft", ["stream_id", "email_id", "draft_eml_url", "screen_url"]),
    ("em", "send"): ("email.send", ["stream_id", "email_id", "sent_eml_url"]),
    ("em", "discard"): ("email.discard", ["stream_id", "email_id"]),
    ("tr", "request"): ("triage.request", ["stream_id", "triage_id", "message_eml_url"]),
    ("tr", "ask"): ("triage.ask", ["stream_id", "triage_id", "adviser_id"]),
    ("tr", "advise"): ("triage.advise", ["stream_id", "triage_id", "verdict"]),
    ("tr", "consider"): ("triage.consider", ["stream_id", "triage_id", "verdict"]),
    ("tr", "reply"): ("triage.reply", ["stream_id", "triage_id", "email_id"]),
    ("tr", "work"): ("triage.work", ["stream_id", "triage_id", "work_id"]),
    ("tr", "ignore"): ("triage.ignore", ["stream_id", "triage_id"]),
    ("tr", "defer"): ("triage.defer", ["stream_id", "triage_id"]),
    ("core", "streamOpen"): ("stream.open", ["proof_revision_url"]),
    ("core", "streamClose"): ("stream.close", ["stream_id"]),
}
ENTRY = re.compile(r"\((pr|em|tr|core) (\w+) \(\.(\w+)((?:\s+(?:[^()\s,]+|\"[^\"]*\"|\(some \"[^\"]*\"\)|\(some \w+\)))*)\)"
                   r"(?:\s+\[([^\]]*)\])?,\s*(none|some \"([^\"]+)\")\)")
ARG = re.compile(r"\(some \"([^\"]*)\"\)|\(some (\w+)\)|\"([^\"]*)\"|(\S+)")


def parse_story(path: str = EXAMPLES):
    """The story as `(request, want)` pairs: the request as the engine takes it, `want` the reason or None."""
    text = open(path, encoding="utf-8").read()
    names = {}
    for name, value in re.findall(r"^def (\w+) : (?:Id|String) :=\s*\"([^\"]+)\"", text, re.M):
        names[name] = value
    eml = re.search(r"^def eml \(n : String\) : String := s!\"([^\"]+)\"", text, re.M).group(1)
    for name, value in re.findall(r"^def (\w+) := eml \"([^\"]+)\"", text, re.M):
        names[name] = eml.replace("{n}", value)
    body = text.split("def story : List (Sv.Req × Option String) :=", 1)[1].split("\ndef answersOk", 1)[0]
    body = re.sub(r"--[^\n]*", "", body)
    story = []
    for helper, actor, ctor, args, fresh, want, reason in ENTRY.findall(body):
        command, fields = CONSTRUCTORS[(helper, ctor)]
        values = []
        for some, named, literal, token in ARG.findall(args):
            if token == "none":
                values.append(None)
            elif token:
                values.append(names[token])
            elif named:
                values.append(names[named])
            elif literal:
                values.append(literal)
            else:
                values.append(some)
        assert len(values) == len(fields) + 1, (ctor, values)
        cmd = {"command": command}
        cmd.update({f: v for f, v in zip(fields, values[:-1]) if v is not None})   # an optional field, absent
        if values[-1] is not None:
            cmd["meta"] = values[-1]
        fresh_ids = [names[x.strip()] for x in fresh.split(",") if x.strip()] if fresh else []
        story.append(({"actor_id": names[actor], "command": cmd, "fresh": fresh_ids},
                      reason if want.startswith("some") else None))
    return story


@pytest.fixture(scope="module")
def story():
    s = parse_story()
    assert len(s) >= 120, "the story is shorter than it was: is the parser reading it?"
    assert {r for _, r in s if r} >= set(M.RULE_NAMES), "the story no longer refuses something under every rule"
    # the rule named twice refuses on both an email command and a triage command
    for reason, cmds in (("only_owner_or_person_delegates_can_decide", ("email.send", "triage.reply")),):
        for c in cmds:
            assert any(r == reason and q["command"]["command"] == c for q, r in s), (reason, c)
    return s


def test_the_model_tells_the_story(story):
    """Every answer the Lean story expects, the model gives, at the Lean's positions."""
    model = M.Model()
    answers = []
    for req, want in story:
        got, _, _, _ = model.step(req)
        answers.append(got)
    wrong = [(i, req["command"]["command"], want, got) for i, ((req, want), got) in enumerate(zip(story, answers))
             if got != want]
    assert not wrong, wrong
    accepted = sum(1 for _, w in story if w is None)
    assert sum(len(s.events) for s in model.streams.values()) == accepted


def test_the_engine_tells_the_story_as_the_model_does(story):
    """The engine's answers to the story are the Lean's and the model's, step by step, positions included."""
    model = M.Model()
    e = Engine([ENGINE])
    e.start()
    try:
        for i, (req, want) in enumerate(story):
            mwant, sid, at, event = model.step(req)
            got = e.decide(req)
            assert mwant == want, (i, req, mwant, want)
            assert "error" not in got, (i, req, got)
            assert got["stream_id"] == sid and got["at"] == at, (i, got, sid, at)
            if want is None:
                assert got["accept"] is True and got["event"] == event, (i, got, event)
            else:
                assert got["accept"] is False and got["reason"] == want, (i, got, want)
        for sid, s in model.streams.items():
            assert e.query({"query": "stream", "stream_id": sid}) == s.read()
    finally:
        e.stop()
