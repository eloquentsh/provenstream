# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Field forms at the boundaries the layer and the wire check: `meta` of exactly 4096 and 4097 UTF-8 bytes, an `.eml`
URL of exactly 2048 and 2049 characters, a URL without the `.eml` ending, a control character in `meta`, an id not in
canonical lowercase form, an unknown key, a missing required field, and their neighbours. For each, the model must
predict `malformed` exactly where the engine answers it, and the prediction must be the one the layer's definitions give.

Each case is sent from the same state (a stream open, one email created), restored between cases from the engine's
snapshot, so the cases do not depend on each other.
"""
from __future__ import annotations
import copy, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))
sys.path.insert(0, os.path.join(REPO, "host"))
sys.path.insert(0, HERE)

import pytest
from provenstream.engine import Engine
import email_model as M

ENGINE = os.environ.get("EMAIL_ENGINE") or os.path.join(REPO, "examples", "email", ".lake", "build", "bin", "email-engine")
ANN = "a0000000-0000-4000-8000-00000000000a"
BEN = "b0000000-0000-4000-8000-00000000000b"
S = "5a000000-0000-7000-8000-00000000000c"
K = "6b000000-0000-7000-8000-00000000000d"
K2 = "6b000000-0000-7000-8000-00000000000e"
for _id in (ANN, BEN, S, K):
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
    ("meta of exactly 4096 bytes (2048 two-byte characters)", (ANN, cmd("email.discard", email_id=K, meta="é" * 2048), []), NOT_MALFORMED),
    ("meta of 4097 bytes", (ANN, cmd("email.discard", email_id=K, meta="é" * 2048 + "a"), []), MALFORMED),
    ("meta of 4096 one-byte characters", (ANN, cmd("email.discard", email_id=K, meta="a" * 4096), []), NOT_MALFORMED),
    ("meta of 4097 one-byte characters", (ANN, cmd("email.discard", email_id=K, meta="a" * 4097), []), MALFORMED),
    ("meta holding a tab", (ANN, cmd("email.discard", email_id=K, meta="a\tb"), []), MALFORMED),
    ("meta holding U+001F", (ANN, cmd("email.discard", email_id=K, meta="a\x1fb"), []), MALFORMED),
    ("meta holding DEL", (ANN, cmd("email.discard", email_id=K, meta="a\x7fb"), []), MALFORMED),
    ("meta holding U+0000", (ANN, cmd("email.discard", email_id=K, meta="a\x00b"), []), MALFORMED),
    ("meta holding a space and non-ASCII text", (ANN, cmd("email.discard", email_id=K, meta="é and 😀"), []), NOT_MALFORMED),
    ("meta given as null", (ANN, cmd("email.discard", email_id=K, meta=None), []), NOT_MALFORMED),
    ("meta given as a number", (ANN, cmd("email.discard", email_id=K, meta=7), []), MALFORMED),
    ("an .eml URL of exactly 2048 characters", (ANN, cmd("email.send", email_id=K, sent_url=eml_of(2048)), []), NOT_MALFORMED),
    ("an .eml URL of 2049 characters", (ANN, cmd("email.send", email_id=K, sent_url=eml_of(2049)), []), MALFORMED),
    ("an .eml URL of 2048 characters that are 4000 bytes", (ANN, cmd("email.send", email_id=K, sent_url="https://" + "é" * 2036 + ".eml"), []), NOT_MALFORMED),
    ("an .eml URL holding a space", (ANN, cmd("email.send", email_id=K, sent_url="https://x/a b.eml"), []), MALFORMED),
    ("an .eml URL holding DEL", (ANN, cmd("email.send", email_id=K, sent_url="https://x/\x7f.eml"), []), MALFORMED),
    ("an .eml URL holding non-ASCII text", (ANN, cmd("email.send", email_id=K, sent_url="https://x/é.eml"), []), NOT_MALFORMED),
    ("a URL with two separators", (ANN, cmd("email.send", email_id=K, sent_url="a://b://c.eml"), []), MALFORMED),
    ("a URL with an empty scheme", (ANN, cmd("email.send", email_id=K, sent_url="://x.eml"), []), MALFORMED),
    ("a URL with nothing after the separator", (ANN, cmd("email.send", email_id=K, sent_url="https://"), []), MALFORMED),
    ("the empty URL", (ANN, cmd("email.send", email_id=K, sent_url=""), []), MALFORMED),
    ("a URL not ending in .eml", (ANN, cmd("email.send", email_id=K, sent_url="https://x/sent"), []), MALFORMED),
    ("a URL ending in .EML (case matters)", (ANN, cmd("email.send", email_id=K, sent_url="https://x/sent.EML"), []), MALFORMED),
    ("a URL ending in .eml with a fragment after it", (ANN, cmd("email.send", email_id=K, sent_url="https://x/sent.eml#sha256=ab"), []), MALFORMED),
    ("a URL whose fragment ends in .eml", (ANN, cmd("email.send", email_id=K, sent_url="https://blobs/b/abcd#sha256=abcd&name=sent.eml"), []), NOT_MALFORMED),
    ("a URL that is only .eml after the scheme", (ANN, cmd("email.send", email_id=K, sent_url="file://.eml"), []), NOT_MALFORMED),
    ("a draft URL not ending in .eml", (BEN, cmd("email.draft", email_id=K, draft_url="https://x/d1"), []), MALFORMED),
    ("a composed URL not ending in .eml", (BEN, cmd("email.compose", email_id=K, composed_url="https://x/c1.txt", screen_url="https://x/s1"), []), MALFORMED),
    ("a screen URL holding a space", (BEN, cmd("email.compose", email_id=K, composed_url="https://x/c1.eml", screen_url="https://x/s 1"), []), MALFORMED),
    ("a screen URL not ending in .eml (a url, not an eml)", (BEN, cmd("email.compose", email_id=K, composed_url="https://x/c1.eml", screen_url="https://x/s1.svg"), []), NOT_MALFORMED),
    ("an uppercase email_id", (ANN, cmd("email.discard", email_id=K.upper()), []), MALFORMED),
    ("an uppercase stream_id", (ANN, cmd("email.discard", email_id=K, stream_id=S.upper()), []), MALFORMED),
    ("an uppercase drafter_id", (ANN, cmd("email.solicit", email_id=K, drafter_id=BEN.upper()), []), MALFORMED),
    ("an uppercase actor_id", (ANN.upper(), cmd("email.discard", email_id=K), []), MALFORMED),
    ("an email_id without hyphens", (ANN, cmd("email.discard", email_id=K.replace("-", "")), []), MALFORMED),
    ("an email_id with braces", (ANN, cmd("email.discard", email_id="{%s}" % K), []), MALFORMED),
    ("an email_id that is a number", (ANN, cmd("email.discard", email_id=5), []), MALFORMED),
    ("an unknown extra key", (ANN, cmd("email.discard", email_id=K, extra=1), []), MALFORMED),
    ("an old field name beside the new", (ANN, cmd("email.send", email_id=K, sent_url="https://x/m.eml", revision_url="https://x/m"), []), MALFORMED),
    ("a missing required field (drafter_id)", (ANN, cmd("email.solicit", email_id=K), []), MALFORMED),
    ("a missing in_reply_to_url (optional)", (ANN, cmd("email.create", email_id=K2), []), NOT_MALFORMED),
    ("an in_reply_to_url given as null", (ANN, cmd("email.create", email_id=K2, in_reply_to_url=None), []), NOT_MALFORMED),
    ("a well-formed in_reply_to_url", (ANN, cmd("email.create", email_id=K2, in_reply_to_url="https://x/in.eml"), []), NOT_MALFORMED),
    ("an in_reply_to_url of exactly 2048 characters", (ANN, cmd("email.create", email_id=K2, in_reply_to_url=eml_of(2048)), []), NOT_MALFORMED),
    ("an in_reply_to_url of 2049 characters", (ANN, cmd("email.create", email_id=K2, in_reply_to_url=eml_of(2049)), []), MALFORMED),
    ("an in_reply_to_url holding a space", (ANN, cmd("email.create", email_id=K2, in_reply_to_url="https://x/i n.eml"), []), MALFORMED),
    ("an in_reply_to_url not ending in .eml", (ANN, cmd("email.create", email_id=K2, in_reply_to_url="https://x/in"), []), MALFORMED),
    ("the empty in_reply_to_url", (ANN, cmd("email.create", email_id=K2, in_reply_to_url=""), []), MALFORMED),
    ("an in_reply_to_url given as a number", (ANN, cmd("email.create", email_id=K2, in_reply_to_url=7), []), MALFORMED),
    ("a missing required field (email_id)", (ANN, cmd("email.discard"), []), MALFORMED),
    ("a missing stream_id", (ANN, {"command": "email.discard", "email_id": K}, []), MALFORMED),
    ("a missing meta (optional)", (ANN, cmd("email.discard", email_id=K), []), NOT_MALFORMED),
    ("a stream_id on an open", (ANN, {"command": "stream.open", "proof_revision_url": M.PROOF_URL, "stream_id": S}, [S]), MALFORMED),
    ("an unknown command", (ANN, cmd("email.nope", email_id=K), []), MALFORMED),
    ("a fresh id not in canonical form", (ANN, cmd("email.discard", email_id=K), ["nope"]), MALFORMED),
    ("a proof URL holding a tab (text, not url: refused by the rule, not the wire)", (ANN, {"command": "stream.open", "proof_revision_url": "https://x/y\tz"}, [K2]), NOT_MALFORMED),
    ("a proof URL holding U+0000", (ANN, {"command": "stream.open", "proof_revision_url": "https://x/y\x00z"}, [K2]), MALFORMED),
]


@pytest.fixture(scope="module")
def engine_and_snapshot():
    e = Engine([ENGINE])
    e.start()
    model = M.Model()
    for req in ({"actor_id": ANN, "command": {"command": "stream.open", "proof_revision_url": M.PROOF_URL}, "fresh": [S]},
                {"actor_id": ANN, "command": cmd("email.create", email_id=K, in_reply_to_url="https://x/in0.eml"), "fresh": []}):
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
