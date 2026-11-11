# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Field forms at the boundaries the layer and the wire check: `meta` of exactly 4096 and 4097 UTF-8 bytes, a URL of
exactly 2048 and 2049 characters, a control character in `meta`, an id not in canonical lowercase form, an unknown key,
a missing required field, and their neighbours. For each, the model must predict `malformed` exactly where the engine
answers it, and the prediction must be the one the layer's definitions give.

Each case is sent from the same state (a stream open, one change created), restored between cases from the engine's
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
import solo_model as M

ENGINE = os.environ.get("SOLO_ENGINE") or os.path.join(REPO, "examples", "solochangecontrol", ".lake", "build", "bin",
                                                        "solochangecontrol-engine")
ANN = "a0000000-0000-4000-8000-00000000000a"
BEN = "b0000000-0000-4000-8000-00000000000b"
S = "5a000000-0000-7000-8000-00000000000c"
K = "6b000000-0000-7000-8000-00000000000d"
K2 = "6b000000-0000-7000-8000-00000000000e"
R0 = "https://example.org/repo/commit/r0"
for _id in (ANN, BEN, S, K):
    assert any(c.isalpha() for c in _id), "the ids must hold letters, or upper-casing them changes nothing"

MALFORMED, NOT_MALFORMED = "malformed", "decoded"


def url_of(n: int) -> str:
    """A URL of exactly `n` characters."""
    head = "https://x/"
    return head + "a" * (n - len(head))


def cmd(name, **f):
    c = {"command": name, "stream_id": S}
    c.update(f)
    return c


# (label, request, what the layer's definitions say: malformed, or decoded)
CASES = [
    ("meta of exactly 4096 bytes (2048 two-byte characters)", (ANN, cmd("change.pull", change_id=K, meta="é" * 2048), []), NOT_MALFORMED),
    ("meta of 4097 bytes", (ANN, cmd("change.pull", change_id=K, meta="é" * 2048 + "a"), []), MALFORMED),
    ("meta of 4096 one-byte characters", (ANN, cmd("change.pull", change_id=K, meta="a" * 4096), []), NOT_MALFORMED),
    ("meta of 4097 one-byte characters", (ANN, cmd("change.pull", change_id=K, meta="a" * 4097), []), MALFORMED),
    ("meta holding a tab", (ANN, cmd("change.pull", change_id=K, meta="a\tb"), []), MALFORMED),
    ("meta holding U+001F", (ANN, cmd("change.pull", change_id=K, meta="a\x1fb"), []), MALFORMED),
    ("meta holding DEL", (ANN, cmd("change.pull", change_id=K, meta="a\x7fb"), []), MALFORMED),
    ("meta holding U+0000", (ANN, cmd("change.pull", change_id=K, meta="a\x00b"), []), MALFORMED),
    ("meta holding a space and non-ASCII text", (ANN, cmd("change.pull", change_id=K, meta="é and 😀"), []), NOT_MALFORMED),
    ("meta given as null", (ANN, cmd("change.pull", change_id=K, meta=None), []), NOT_MALFORMED),
    ("meta given as a number", (ANN, cmd("change.pull", change_id=K, meta=7), []), MALFORMED),
    ("a URL of exactly 2048 characters", (ANN, cmd("change.merge", change_id=K, merged_revision_url=url_of(2048)), []), NOT_MALFORMED),
    ("a URL of 2049 characters", (ANN, cmd("change.merge", change_id=K, merged_revision_url=url_of(2049)), []), MALFORMED),
    ("a URL of 2048 characters that are 4096 bytes", (ANN, cmd("change.merge", change_id=K, merged_revision_url="https://" + "é" * 2040), []), NOT_MALFORMED),
    ("a URL holding a space", (ANN, cmd("change.merge", change_id=K, merged_revision_url="https://x/a b"), []), MALFORMED),
    ("a URL holding DEL", (ANN, cmd("change.merge", change_id=K, merged_revision_url="https://x/\x7f"), []), MALFORMED),
    ("a URL holding non-ASCII text", (ANN, cmd("change.merge", change_id=K, merged_revision_url="https://x/é"), []), NOT_MALFORMED),
    ("a URL with two separators", (ANN, cmd("change.merge", change_id=K, merged_revision_url="a://b://c"), []), MALFORMED),
    ("a URL with an empty scheme", (ANN, cmd("change.merge", change_id=K, merged_revision_url="://x"), []), MALFORMED),
    ("a URL with nothing after the separator", (ANN, cmd("change.merge", change_id=K, merged_revision_url="https://"), []), MALFORMED),
    ("the empty URL", (ANN, cmd("change.merge", change_id=K, merged_revision_url=""), []), MALFORMED),
    ("a screen URL holding a space", (BEN, cmd("change.review", change_id=K, reviewed_revision_url="https://x/c1", screen_url="https://x/s 1"), []), MALFORMED),
    ("an uppercase change_id", (ANN, cmd("change.pull", change_id=K.upper()), []), MALFORMED),
    ("an uppercase stream_id", (ANN, cmd("change.pull", change_id=K, stream_id=S.upper()), []), MALFORMED),
    ("an uppercase developer_id", (ANN, cmd("change.branch", change_id=K, developer_id=BEN.upper(), branch_revision_url="https://x/b1"), []), MALFORMED),
    ("an uppercase actor_id", (ANN.upper(), cmd("change.pull", change_id=K), []), MALFORMED),
    ("a change_id without hyphens", (ANN, cmd("change.pull", change_id=K.replace("-", "")), []), MALFORMED),
    ("a change_id with braces", (ANN, cmd("change.pull", change_id="{%s}" % K), []), MALFORMED),
    ("a change_id that is a number", (ANN, cmd("change.pull", change_id=5), []), MALFORMED),
    ("an unknown extra key", (ANN, cmd("change.pull", change_id=K, extra=1), []), MALFORMED),
    ("an old field name beside the new", (ANN, cmd("change.merge", change_id=K, merged_revision_url="https://x/m", revision_url="https://x/m"), []), MALFORMED),
    ("a missing required field (from_revision_url)", (ANN, cmd("change.create", change_id=K2), []), MALFORMED),
    ("a missing harness_revision_url (optional)", (ANN, cmd("change.create", change_id=K2, from_revision_url="https://x/k2"), []), NOT_MALFORMED),
    ("a harness_revision_url given as null", (ANN, cmd("change.create", change_id=K2, from_revision_url="https://x/k2", harness_revision_url=None), []), NOT_MALFORMED),
    ("a well-formed harness_revision_url", (ANN, cmd("change.create", change_id=K2, from_revision_url="https://x/k2", harness_revision_url="https://x/h1"), []), NOT_MALFORMED),
    ("a harness_revision_url of exactly 2048 characters", (ANN, cmd("change.create", change_id=K2, from_revision_url="https://x/k2", harness_revision_url=url_of(2048)), []), NOT_MALFORMED),
    ("a harness_revision_url of 2049 characters", (ANN, cmd("change.create", change_id=K2, from_revision_url="https://x/k2", harness_revision_url=url_of(2049)), []), MALFORMED),
    ("a harness_revision_url holding a space", (ANN, cmd("change.create", change_id=K2, from_revision_url="https://x/k2", harness_revision_url="https://x/h 1"), []), MALFORMED),
    ("the empty harness_revision_url", (ANN, cmd("change.create", change_id=K2, from_revision_url="https://x/k2", harness_revision_url=""), []), MALFORMED),
    ("a harness_revision_url given as a number", (ANN, cmd("change.create", change_id=K2, from_revision_url="https://x/k2", harness_revision_url=7), []), MALFORMED),
    ("a missing required field (change_id)", (ANN, cmd("change.pull"), []), MALFORMED),
    ("a missing stream_id", (ANN, {"command": "change.pull", "change_id": K}, []), MALFORMED),
    ("a missing meta (optional)", (ANN, cmd("change.pull", change_id=K), []), NOT_MALFORMED),
    ("a stream_id on an open", (ANN, {"command": "stream.open", "proof_revision_url": M.PROOF_URL, "stream_id": S}, [S]), MALFORMED),
    ("an unknown command", (ANN, cmd("change.nope", change_id=K), []), MALFORMED),
    ("a fresh id not in canonical form", (ANN, cmd("change.pull", change_id=K), ["nope"]), MALFORMED),
    ("a proof URL holding a tab (text, not url: refused by the rule, not the wire)", (ANN, {"command": "stream.open", "proof_revision_url": "https://x/y\tz"}, [K2]), NOT_MALFORMED),
    ("a proof URL holding U+0000", (ANN, {"command": "stream.open", "proof_revision_url": "https://x/y\x00z"}, [K2]), MALFORMED),
]


@pytest.fixture(scope="module")
def engine_and_snapshot():
    e = Engine([ENGINE])
    e.start()
    model = M.Model()
    for req in ({"actor_id": ANN, "command": {"command": "stream.open", "proof_revision_url": M.PROOF_URL}, "fresh": [S]},
                {"actor_id": ANN, "command": cmd("change.create", change_id=K, from_revision_url=R0), "fresh": []}):
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
