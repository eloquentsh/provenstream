# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Field forms at the boundaries the layer and the wire check: `meta` of exactly 4096 and 4097 UTF-8 bytes, a message URL of exactly 2048 and 2049
characters, a URL without the `.eml` ending, a verdict that is neither reply nor ignore, a control character in `meta`, an id not in
canonical lowercase form, an unknown key, a missing required field, and their neighbours. For each, the model must
predict `malformed` exactly where the engine answers it, and the prediction must be the one the layer's definitions give.

Each case is sent from the same state (a stream open, one triage created), restored between cases from the engine's
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
import triage_model as M

ENGINE = os.environ.get("TRIAGE_ENGINE") or os.path.join(REPO, "examples", "emailtriage", ".lake", "build", "bin", "emailtriage-engine")
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
    ("meta of exactly 4096 bytes (2048 two-byte characters)", (ANN, cmd("triage.ignore", triage_id=K, meta="é" * 2048), []), NOT_MALFORMED),
    ("meta of 4097 bytes", (ANN, cmd("triage.ignore", triage_id=K, meta="é" * 2048 + "a"), []), MALFORMED),
    ("meta of 4096 one-byte characters", (ANN, cmd("triage.ignore", triage_id=K, meta="a" * 4096), []), NOT_MALFORMED),
    ("meta of 4097 one-byte characters", (ANN, cmd("triage.ignore", triage_id=K, meta="a" * 4097), []), MALFORMED),
    ("meta holding a tab", (ANN, cmd("triage.ignore", triage_id=K, meta="a\tb"), []), MALFORMED),
    ("meta holding U+0000", (ANN, cmd("triage.ignore", triage_id=K, meta="a\x00b"), []), MALFORMED),
    ("meta holding a space and non-ASCII text", (ANN, cmd("triage.ignore", triage_id=K, meta="é and 😀"), []), NOT_MALFORMED),
    ("meta given as null", (ANN, cmd("triage.ignore", triage_id=K, meta=None), []), NOT_MALFORMED),
    ("meta given as a number", (ANN, cmd("triage.ignore", triage_id=K, meta=7), []), MALFORMED),
    ("a message URL of exactly 2048 characters", (ANN, cmd("triage.create", triage_id=K2, message_url=eml_of(2048)), []), NOT_MALFORMED),
    ("a message URL of 2049 characters", (ANN, cmd("triage.create", triage_id=K2, message_url=eml_of(2049)), []), MALFORMED),
    ("a message URL holding a space", (ANN, cmd("triage.create", triage_id=K2, message_url="https://x/a b.eml"), []), MALFORMED),
    ("a message URL holding non-ASCII text", (ANN, cmd("triage.create", triage_id=K2, message_url="eloquentmail://personal/é.eml"), []), NOT_MALFORMED),
    ("a message URL with two separators", (ANN, cmd("triage.create", triage_id=K2, message_url="a://b://c.eml"), []), MALFORMED),
    ("a message URL with an empty scheme", (ANN, cmd("triage.create", triage_id=K2, message_url="://x.eml"), []), MALFORMED),
    ("the empty message URL", (ANN, cmd("triage.create", triage_id=K2, message_url=""), []), MALFORMED),
    ("a message URL not ending in .eml", (ANN, cmd("triage.create", triage_id=K2, message_url="eloquentmail://personal/abc"), []), MALFORMED),
    ("a message URL ending in .EML (case matters)", (ANN, cmd("triage.create", triage_id=K2, message_url="eloquentmail://personal/abc.EML"), []), MALFORMED),
    ("a missing message URL", (ANN, cmd("triage.create", triage_id=K2), []), MALFORMED),
    ("the verdict reply", (BEN, cmd("triage.review", triage_id=K, verdict="reply"), []), NOT_MALFORMED),
    ("the verdict ignore", (BEN, cmd("triage.review", triage_id=K, verdict="ignore"), []), NOT_MALFORMED),
    ("the verdict work", (BEN, cmd("triage.review", triage_id=K, verdict="work"), []), NOT_MALFORMED),
    ("the verdict Reply (case matters)", (BEN, cmd("triage.review", triage_id=K, verdict="Reply"), []), MALFORMED),
    ("the verdict delegate", (BEN, cmd("triage.review", triage_id=K, verdict="delegate"), []), MALFORMED),
    ("the empty verdict", (BEN, cmd("triage.review", triage_id=K, verdict=""), []), MALFORMED),
    ("a verdict with a trailing space", (BEN, cmd("triage.review", triage_id=K, verdict="reply "), []), MALFORMED),
    ("a verdict given as a number", (BEN, cmd("triage.review", triage_id=K, verdict=1), []), MALFORMED),
    ("a verdict given as null", (BEN, cmd("triage.review", triage_id=K, verdict=None), []), MALFORMED),
    ("a missing verdict", (BEN, cmd("triage.advise", triage_id=K), []), MALFORMED),
    ("an advice verdict that is not a verdict", (BEN, cmd("triage.advise", triage_id=K, verdict="maybe"), []), MALFORMED),
    ("an uppercase triage_id", (ANN, cmd("triage.ignore", triage_id=K.upper()), []), MALFORMED),
    ("an uppercase stream_id", (ANN, cmd("triage.ignore", triage_id=K, stream_id=S.upper()), []), MALFORMED),
    ("an uppercase adviser_id", (ANN, cmd("triage.ask", triage_id=K, adviser_id=BEN.upper()), []), MALFORMED),
    ("an uppercase email_id on a reply", (ANN, cmd("triage.reply", triage_id=K, email_id=K2.upper()), []), MALFORMED),
    ("an email_id that is a number", (ANN, cmd("triage.reply", triage_id=K, email_id=5), []), MALFORMED),
    ("a missing email_id on a reply", (ANN, cmd("triage.reply", triage_id=K), []), MALFORMED),
    ("an uppercase actor_id", (ANN.upper(), cmd("triage.ignore", triage_id=K), []), MALFORMED),
    ("a triage_id without hyphens", (ANN, cmd("triage.ignore", triage_id=K.replace("-", "")), []), MALFORMED),
    ("a triage_id that is a number", (ANN, cmd("triage.ignore", triage_id=5), []), MALFORMED),
    ("an unknown extra key", (ANN, cmd("triage.ignore", triage_id=K, extra=1), []), MALFORMED),
    ("a missing required field (adviser_id)", (ANN, cmd("triage.ask", triage_id=K), []), MALFORMED),
    ("a missing required field (triage_id)", (ANN, cmd("triage.ignore"), []), MALFORMED),
    ("a missing stream_id", (ANN, {"command": "triage.ignore", "triage_id": K}, []), MALFORMED),
    ("a missing meta (optional)", (ANN, cmd("triage.ignore", triage_id=K), []), NOT_MALFORMED),
    ("a stream_id on an open", (ANN, {"command": "stream.open", "proof_revision_url": M.PROOF_URL, "stream_id": S}, [S]), MALFORMED),
    ("an unknown command", (ANN, cmd("triage.nope", triage_id=K), []), MALFORMED),
    ("a fresh id not in canonical form", (ANN, cmd("triage.ignore", triage_id=K), ["nope"]), MALFORMED),
    ("a proof URL holding a tab (text, not url: refused by the rule, not the wire)", (ANN, {"command": "stream.open", "proof_revision_url": "https://x/y\tz"}, [K2]), NOT_MALFORMED),
    ("a proof URL holding U+0000", (ANN, {"command": "stream.open", "proof_revision_url": "https://x/y\x00z"}, [K2]), MALFORMED),
]


@pytest.fixture(scope="module")
def engine_and_snapshot():
    e = Engine([ENGINE])
    e.start()
    model = M.Model()
    for req in ({"actor_id": ANN, "command": {"command": "stream.open", "proof_revision_url": M.PROOF_URL}, "fresh": [S]},
                {"actor_id": ANN, "command": cmd("triage.create", triage_id=K, message_url="eloquentmail://personal/in0.eml"), "fresh": []}):
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
