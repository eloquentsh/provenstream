# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Field forms at the boundaries the layer and the wire check, for both proofs' commands. The email cases are
examples/email/tests/test_fields.py's, the triage cases examples/emailtriage/tests/test_fields.py's, each label marked
with its proof. For each, the model must predict `malformed` exactly where the engine answers it. The prediction must
be the one the layer's definitions give.

Each case is sent from the same state: a stream open, one email created, one triage requested. The engine's snapshot
restores that state between cases, so the cases do not depend on each other.
"""
from __future__ import annotations
import copy, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(REPO, "host"))
sys.path.insert(0, HERE)

import pytest
from provenstream.engine import Engine
import mailbox_model as M

ENGINE = os.environ.get("MAILBOX_ENGINE") or os.path.join(REPO, "examples", "email-triage-and-reply", ".lake", "build",
                                                          "bin", "email-triage-and-reply-engine")
ANN = "a0000000-0000-4000-8000-00000000000a"
BEN = "b0000000-0000-4000-8000-00000000000b"
S = "5a000000-0000-7000-8000-00000000000c"
K = "6b000000-0000-7000-8000-00000000000d"      # the email
K2 = "6b000000-0000-7000-8000-00000000000e"
TK = "7c000000-0000-7000-8000-00000000000d"     # the triage
TK2 = "7c000000-0000-7000-8000-00000000000e"
for _id in (ANN, BEN, S, K, TK):
    assert any(c.isalpha() for c in _id), "the ids must hold letters, or upper-casing them changes nothing"

MALFORMED, NOT_MALFORMED = "malformed", "decoded"


def eml_of(n: int) -> str:
    """An .eml URL of exactly `n` characters."""
    head, tail = "https://x/", ".eml"
    return head + "a" * (n - len(head) - len(tail)) + tail


def cmd(name, **f):
    c = {"command": name, "stream_id": S}
    c.update(f)
    return c


# (label, request, what the layer's definitions say: malformed, or decoded)
CASES = [
    ("email: meta of exactly 4096 bytes (2048 two-byte characters)", (ANN, cmd("email.discard", email_id=K, meta="é" * 2048), []), NOT_MALFORMED),
    ("email: meta of 4097 bytes", (ANN, cmd("email.discard", email_id=K, meta="é" * 2048 + "a"), []), MALFORMED),
    ("email: meta of 4096 one-byte characters", (ANN, cmd("email.discard", email_id=K, meta="a" * 4096), []), NOT_MALFORMED),
    ("email: meta of 4097 one-byte characters", (ANN, cmd("email.discard", email_id=K, meta="a" * 4097), []), MALFORMED),
    ("email: meta holding a tab", (ANN, cmd("email.discard", email_id=K, meta="a\tb"), []), MALFORMED),
    ("email: meta holding U+001F", (ANN, cmd("email.discard", email_id=K, meta="a\x1fb"), []), MALFORMED),
    ("email: meta holding DEL", (ANN, cmd("email.discard", email_id=K, meta="a\x7fb"), []), MALFORMED),
    ("email: meta holding U+0000", (ANN, cmd("email.discard", email_id=K, meta="a\x00b"), []), MALFORMED),
    ("email: meta holding a space and non-ASCII text", (ANN, cmd("email.discard", email_id=K, meta="é and 😀"), []), NOT_MALFORMED),
    ("email: meta given as null", (ANN, cmd("email.discard", email_id=K, meta=None), []), NOT_MALFORMED),
    ("email: meta given as a number", (ANN, cmd("email.discard", email_id=K, meta=7), []), MALFORMED),
    ("email: an .eml URL of exactly 2048 characters", (ANN, cmd("email.send", email_id=K, sent_eml_url=eml_of(2048)), []), NOT_MALFORMED),
    ("email: an .eml URL of 2049 characters", (ANN, cmd("email.send", email_id=K, sent_eml_url=eml_of(2049)), []), MALFORMED),
    ("email: an .eml URL of 2048 characters that are 4000 bytes", (ANN, cmd("email.send", email_id=K, sent_eml_url="https://" + "é" * 2036 + ".eml"), []), NOT_MALFORMED),
    ("email: an .eml URL holding a space", (ANN, cmd("email.send", email_id=K, sent_eml_url="https://x/a b.eml"), []), MALFORMED),
    ("email: an .eml URL holding DEL", (ANN, cmd("email.send", email_id=K, sent_eml_url="https://x/\x7f.eml"), []), MALFORMED),
    ("email: an .eml URL holding non-ASCII text", (ANN, cmd("email.send", email_id=K, sent_eml_url="https://x/é.eml"), []), NOT_MALFORMED),
    ("email: a URL with two separators", (ANN, cmd("email.send", email_id=K, sent_eml_url="a://b://c.eml"), []), MALFORMED),
    ("email: a URL with an empty scheme", (ANN, cmd("email.send", email_id=K, sent_eml_url="://x.eml"), []), MALFORMED),
    ("email: a URL with nothing after the separator", (ANN, cmd("email.send", email_id=K, sent_eml_url="https://"), []), MALFORMED),
    ("email: the empty URL", (ANN, cmd("email.send", email_id=K, sent_eml_url=""), []), MALFORMED),
    ("email: a URL not ending in .eml", (ANN, cmd("email.send", email_id=K, sent_eml_url="https://x/sent"), []), MALFORMED),
    ("email: a URL ending in .EML (case matters)", (ANN, cmd("email.send", email_id=K, sent_eml_url="https://x/sent.EML"), []), MALFORMED),
    ("email: a URL ending in .eml with a fragment after it", (ANN, cmd("email.send", email_id=K, sent_eml_url="https://x/sent.eml#sha256=ab"), []), MALFORMED),
    ("email: a URL whose fragment ends in .eml", (ANN, cmd("email.send", email_id=K, sent_eml_url="https://blobs/b/abcd#sha256=abcd&name=sent.eml"), []), NOT_MALFORMED),
    ("email: a URL that is only .eml after the scheme", (ANN, cmd("email.send", email_id=K, sent_eml_url="file://.eml"), []), NOT_MALFORMED),
    ("email: a preparation URL not ending in .eml (a url, not an eml)", (BEN, cmd("email.prepare", email_id=K, preparation_url="https://x/p1"), []), NOT_MALFORMED),
    ("email: a preparation URL holding a space", (BEN, cmd("email.prepare", email_id=K, preparation_url="https://x/p 1"), []), MALFORMED),
    ("email: the empty preparation URL", (BEN, cmd("email.prepare", email_id=K, preparation_url=""), []), MALFORMED),
    ("email: a draft URL not ending in .eml", (BEN, cmd("email.draft", email_id=K, draft_eml_url="https://x/c1.txt", screen_url="https://x/s1"), []), MALFORMED),
    ("email: a screen URL holding a space", (BEN, cmd("email.draft", email_id=K, draft_eml_url="https://x/c1.eml", screen_url="https://x/s 1"), []), MALFORMED),
    ("email: a screen URL not ending in .eml (a url, not an eml)", (BEN, cmd("email.draft", email_id=K, draft_eml_url="https://x/c1.eml", screen_url="https://x/s1.svg"), []), NOT_MALFORMED),
    ("email: a missing screen URL", (BEN, cmd("email.draft", email_id=K, draft_eml_url="https://x/c1.eml"), []), MALFORMED),
    ("email: an uppercase email_id", (ANN, cmd("email.discard", email_id=K.upper()), []), MALFORMED),
    ("email: an uppercase stream_id", (ANN, cmd("email.discard", email_id=K, stream_id=S.upper()), []), MALFORMED),
    ("email: an uppercase preparer_id", (ANN, cmd("email.solicit", email_id=K, preparer_id=BEN.upper()), []), MALFORMED),
    ("email: an uppercase actor_id", (ANN.upper(), cmd("email.discard", email_id=K), []), MALFORMED),
    ("email: an email_id without hyphens", (ANN, cmd("email.discard", email_id=K.replace("-", "")), []), MALFORMED),
    ("email: an email_id with braces", (ANN, cmd("email.discard", email_id="{%s}" % K), []), MALFORMED),
    ("email: an email_id that is a number", (ANN, cmd("email.discard", email_id=5), []), MALFORMED),
    ("email: an unknown extra key", (ANN, cmd("email.discard", email_id=K, extra=1), []), MALFORMED),
    ("email: an old field name beside the new", (ANN, cmd("email.send", email_id=K, sent_eml_url="https://x/m.eml", revision_url="https://x/m"), []), MALFORMED),
    ("email: a missing required field (preparer_id)", (ANN, cmd("email.solicit", email_id=K), []), MALFORMED),
    ("email: a missing in_reply_to_eml_url (optional)", (ANN, cmd("email.create", email_id=K2), []), NOT_MALFORMED),
    ("email: an in_reply_to_eml_url given as null", (ANN, cmd("email.create", email_id=K2, in_reply_to_eml_url=None), []), NOT_MALFORMED),
    ("email: a well-formed in_reply_to_eml_url", (ANN, cmd("email.create", email_id=K2, in_reply_to_eml_url="https://x/in.eml"), []), NOT_MALFORMED),
    ("email: an in_reply_to_eml_url of exactly 2048 characters", (ANN, cmd("email.create", email_id=K2, in_reply_to_eml_url=eml_of(2048)), []), NOT_MALFORMED),
    ("email: an in_reply_to_eml_url of 2049 characters", (ANN, cmd("email.create", email_id=K2, in_reply_to_eml_url=eml_of(2049)), []), MALFORMED),
    ("email: an in_reply_to_eml_url holding a space", (ANN, cmd("email.create", email_id=K2, in_reply_to_eml_url="https://x/i n.eml"), []), MALFORMED),
    ("email: an in_reply_to_eml_url not ending in .eml", (ANN, cmd("email.create", email_id=K2, in_reply_to_eml_url="https://x/in"), []), MALFORMED),
    ("email: the empty in_reply_to_eml_url", (ANN, cmd("email.create", email_id=K2, in_reply_to_eml_url=""), []), MALFORMED),
    ("email: an in_reply_to_eml_url given as a number", (ANN, cmd("email.create", email_id=K2, in_reply_to_eml_url=7), []), MALFORMED),
    ("email: a missing required field (email_id)", (ANN, cmd("email.discard"), []), MALFORMED),
    ("email: a missing stream_id", (ANN, {"command": "email.discard", "email_id": K}, []), MALFORMED),
    ("email: a missing meta (optional)", (ANN, cmd("email.discard", email_id=K), []), NOT_MALFORMED),
    ("email: an unknown command", (ANN, cmd("email.nope", email_id=K), []), MALFORMED),
    ("email: a fresh id not in canonical form", (ANN, cmd("email.discard", email_id=K), ["nope"]), MALFORMED),
    ("triage: meta of exactly 4096 bytes (2048 two-byte characters)", (ANN, cmd("triage.ignore", triage_id=TK, meta="é" * 2048), []), NOT_MALFORMED),
    ("triage: meta of 4097 bytes", (ANN, cmd("triage.ignore", triage_id=TK, meta="é" * 2048 + "a"), []), MALFORMED),
    ("triage: meta of 4096 one-byte characters", (ANN, cmd("triage.ignore", triage_id=TK, meta="a" * 4096), []), NOT_MALFORMED),
    ("triage: meta of 4097 one-byte characters", (ANN, cmd("triage.ignore", triage_id=TK, meta="a" * 4097), []), MALFORMED),
    ("triage: meta holding a tab", (ANN, cmd("triage.ignore", triage_id=TK, meta="a\tb"), []), MALFORMED),
    ("triage: meta holding U+0000", (ANN, cmd("triage.ignore", triage_id=TK, meta="a\x00b"), []), MALFORMED),
    ("triage: meta holding a space and non-ASCII text", (ANN, cmd("triage.ignore", triage_id=TK, meta="é and 😀"), []), NOT_MALFORMED),
    ("triage: meta given as null", (ANN, cmd("triage.ignore", triage_id=TK, meta=None), []), NOT_MALFORMED),
    ("triage: meta given as a number", (ANN, cmd("triage.ignore", triage_id=TK, meta=7), []), MALFORMED),
    ("triage: a message URL of exactly 2048 characters", (ANN, cmd("triage.request", triage_id=TK2, message_eml_url=eml_of(2048)), []), NOT_MALFORMED),
    ("triage: a message URL of 2049 characters", (ANN, cmd("triage.request", triage_id=TK2, message_eml_url=eml_of(2049)), []), MALFORMED),
    ("triage: a message URL holding a space", (ANN, cmd("triage.request", triage_id=TK2, message_eml_url="https://x/a b.eml"), []), MALFORMED),
    ("triage: a message URL holding non-ASCII text", (ANN, cmd("triage.request", triage_id=TK2, message_eml_url="eloquentmail://personal/é.eml"), []), NOT_MALFORMED),
    ("triage: a message URL with two separators", (ANN, cmd("triage.request", triage_id=TK2, message_eml_url="a://b://c.eml"), []), MALFORMED),
    ("triage: a message URL with an empty scheme", (ANN, cmd("triage.request", triage_id=TK2, message_eml_url="://x.eml"), []), MALFORMED),
    ("triage: the empty message URL", (ANN, cmd("triage.request", triage_id=TK2, message_eml_url=""), []), MALFORMED),
    ("triage: a message URL not ending in .eml", (ANN, cmd("triage.request", triage_id=TK2, message_eml_url="eloquentmail://personal/abc"), []), MALFORMED),
    ("triage: a message URL ending in .EML (case matters)", (ANN, cmd("triage.request", triage_id=TK2, message_eml_url="eloquentmail://personal/abc.EML"), []), MALFORMED),
    ("triage: a missing message URL", (ANN, cmd("triage.request", triage_id=TK2), []), MALFORMED),
    ("triage: the verdict reply", (BEN, cmd("triage.consider", triage_id=TK, verdict="reply"), []), NOT_MALFORMED),
    ("triage: the verdict ignore", (BEN, cmd("triage.consider", triage_id=TK, verdict="ignore"), []), NOT_MALFORMED),
    ("triage: the verdict work", (BEN, cmd("triage.consider", triage_id=TK, verdict="work"), []), NOT_MALFORMED),
    ("triage: the verdict defer", (BEN, cmd("triage.consider", triage_id=TK, verdict="defer"), []), NOT_MALFORMED),
    ("triage: the verdict Defer (case matters)", (BEN, cmd("triage.consider", triage_id=TK, verdict="Defer"), []), MALFORMED),
    ("triage: the verdict Reply (case matters)", (BEN, cmd("triage.consider", triage_id=TK, verdict="Reply"), []), MALFORMED),
    ("triage: the verdict delegate", (BEN, cmd("triage.consider", triage_id=TK, verdict="delegate"), []), MALFORMED),
    ("triage: the empty verdict", (BEN, cmd("triage.consider", triage_id=TK, verdict=""), []), MALFORMED),
    ("triage: a verdict with a trailing space", (BEN, cmd("triage.consider", triage_id=TK, verdict="reply "), []), MALFORMED),
    ("triage: a verdict given as a number", (BEN, cmd("triage.consider", triage_id=TK, verdict=1), []), MALFORMED),
    ("triage: a verdict given as null", (BEN, cmd("triage.consider", triage_id=TK, verdict=None), []), MALFORMED),
    ("triage: a missing verdict", (BEN, cmd("triage.advise", triage_id=TK), []), MALFORMED),
    ("triage: an advice verdict that is not a verdict", (BEN, cmd("triage.advise", triage_id=TK, verdict="maybe"), []), MALFORMED),
    ("triage: an uppercase triage_id", (ANN, cmd("triage.ignore", triage_id=TK.upper()), []), MALFORMED),
    ("triage: an uppercase stream_id", (ANN, cmd("triage.ignore", triage_id=TK, stream_id=S.upper()), []), MALFORMED),
    ("triage: an uppercase adviser_id", (ANN, cmd("triage.ask", triage_id=TK, adviser_id=BEN.upper()), []), MALFORMED),
    ("triage: an uppercase email_id on a reply", (ANN, cmd("triage.reply", triage_id=TK, email_id=K2.upper()), []), MALFORMED),
    ("triage: an email_id that is a number", (ANN, cmd("triage.reply", triage_id=TK, email_id=5), []), MALFORMED),
    ("triage: a missing email_id on a reply", (ANN, cmd("triage.reply", triage_id=TK), []), MALFORMED),
    ("triage: an uppercase actor_id", (ANN.upper(), cmd("triage.ignore", triage_id=TK), []), MALFORMED),
    ("triage: a triage_id without hyphens", (ANN, cmd("triage.ignore", triage_id=TK.replace("-", "")), []), MALFORMED),
    ("triage: a triage_id that is a number", (ANN, cmd("triage.ignore", triage_id=5), []), MALFORMED),
    ("triage: an unknown extra key", (ANN, cmd("triage.ignore", triage_id=TK, extra=1), []), MALFORMED),
    ("triage: a missing required field (adviser_id)", (ANN, cmd("triage.ask", triage_id=TK), []), MALFORMED),
    ("triage: a missing required field (triage_id)", (ANN, cmd("triage.ignore"), []), MALFORMED),
    ("triage: a missing stream_id", (ANN, {"command": "triage.ignore", "triage_id": TK}, []), MALFORMED),
    ("triage: a missing meta (optional)", (ANN, cmd("triage.ignore", triage_id=TK), []), NOT_MALFORMED),
    ("triage: an unknown command", (ANN, cmd("triage.nope", triage_id=TK), []), MALFORMED),
    ("triage: a fresh id not in canonical form", (ANN, cmd("triage.ignore", triage_id=TK), ["nope"]), MALFORMED),
    ("a stream_id on an open", (ANN, {"command": "stream.open", "proof_revision_url": M.PROOF_URL, "stream_id": S}, [S]), MALFORMED),
    ("a proof URL holding a tab (text, not url: refused by the rule, not the wire)", (ANN, {"command": "stream.open", "proof_revision_url": "https://x/y\tz"}, [K2]), NOT_MALFORMED),
    ("a proof URL holding U+0000", (ANN, {"command": "stream.open", "proof_revision_url": "https://x/y\x00z"}, [K2]), MALFORMED),
    ("principal: an invite", (ANN, cmd("principal.invite", principal_id=BEN), []), NOT_MALFORMED),
    ("principal: an uppercase principal_id", (ANN, cmd("principal.invite", principal_id=BEN.upper()), []), MALFORMED),
    ("principal: a missing principal_id", (ANN, cmd("principal.summon"), []), MALFORMED),
    ("principal: a summon with meta", (ANN, cmd("principal.summon", principal_id=BEN, meta="an agent"), []), NOT_MALFORMED),
    ("principal: a delegate_id that is a number", (ANN, cmd("principal.delegate", delegate_id=5), []), MALFORMED),
    ("principal: a missing delegate_id", (ANN, cmd("principal.delegate"), []), MALFORMED),
    ("principal: a revoke, no longer a command", (ANN, cmd("principal.revoke", delegate_id=BEN), []), MALFORMED),
    ("principal: a delegate_id beside a principal_id", (ANN, cmd("principal.delegate", delegate_id=BEN, principal_id=BEN), []), MALFORMED),
    ("triage: a reply naming the created email (decoded; the new rule accepts it)", (ANN, cmd("triage.reply", triage_id=TK, email_id=K), []), NOT_MALFORMED),
    ("triage: a reply naming an email not on the stream (decoded; the new rule refuses it)", (ANN, cmd("triage.reply", triage_id=TK, email_id=K2), []), NOT_MALFORMED),
]


@pytest.fixture(scope="module")
def engine_and_snapshot():
    e = Engine([ENGINE])
    e.start()
    model = M.Model()
    for req in ({"actor_id": ANN, "command": {"command": "stream.open", "proof_revision_url": M.PROOF_URL}, "fresh": [S]},
                {"actor_id": ANN, "command": cmd("email.create", email_id=K, in_reply_to_eml_url="https://x/in0.eml"), "fresh": []},
                {"actor_id": ANN, "command": cmd("triage.request", triage_id=TK, message_eml_url="eloquentmail://personal/in0.eml"), "fresh": []}):
        want, _, _, _ = model.step(req)
        assert want is None
        assert e.decide(req)["accept"] is True
    snap = e.snapshot(S)
    yield e, model, snap
    e.stop()


@pytest.mark.parametrize("label,request_,form", CASES, ids=[c[0] for c in CASES])
def test_field_form(engine_and_snapshot, label, request_, form):
    e, model, snap = engine_and_snapshot
    actor, command, fresh = request_
    req = {"actor_id": actor, "command": command, "fresh": fresh}
    predicted, _, _, _ = copy.deepcopy(model).step(req)      # the model's answer, on the stream the request names
    got = e.decide(req)
    e.load(S, snap["k"], snap["state"])                 # the same state for the next case
    assert (predicted == "malformed") == (form == MALFORMED), "the model's prediction is not the layer's: %r" % predicted
    assert (got.get("error") == "malformed") == (predicted == "malformed"), (predicted, got)
    if predicted != "malformed":
        # decoded: the engine's answer is still the model's, reason or acceptance
        if predicted is None:
            assert got["accept"] is True, got
        else:
            assert got["accept"] is False and got["reason"] == predicted, (got, predicted)
    assert e.query({"query": "stream", "stream_id": S}) == model.stream(S).read()


def test_the_cases_reach_the_new_rule():
    """The two reply cases meet the new rule as the model says: one accepted, one refused by it."""
    labels = {c[0]: c for c in CASES}
    model = M.Model()
    for req in ({"actor_id": ANN, "command": {"command": "stream.open", "proof_revision_url": M.PROOF_URL}, "fresh": [S]},
                {"actor_id": ANN, "command": cmd("email.create", email_id=K), "fresh": []},
                {"actor_id": ANN, "command": cmd("triage.request", triage_id=TK, message_eml_url="https://x/m.eml"), "fresh": []}):
        model.step(req)
    ok = labels["triage: a reply naming the created email (decoded; the new rule accepts it)"][1]
    bad = labels["triage: a reply naming an email not on the stream (decoded; the new rule refuses it)"][1]
    assert copy.deepcopy(model).step({"actor_id": ok[0], "command": ok[1], "fresh": ok[2]})[0] is None
    assert copy.deepcopy(model).step({"actor_id": bad[0], "command": bad[1], "fresh": bad[2]})[0] == \
        "reply_must_name_an_unclaimed_email"
