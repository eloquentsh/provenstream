# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The per-stream hash chain and the salted meta commitments (chain.py), where no conformance sequence reaches:
concurrent writers, salts, legacy rows, rows changed after the fact, erased meta. That every receipt is the head the
rows recompute, and that a retry keeps its receipt, the conformance suite checks on every carrier (each sequence's
`stream.rows`, `check: chain`; the idempotency theme)."""
import copy, json, os, subprocess, threading

from conftest import ROOT, U, revision_map

from provenstream import chain, wire
from provenstream.engine import Engine
from provenstream.service import Accepted, Principal, Service


def url(engines):
    return engines["urls"]["tasks"]


def rows_of(store, s):
    return [chain.Row(seq, wire.loads(r), wire.loads(e), salt, ch) for seq, r, e, salt, ch in store.read_chained(s)]


def fill(service, engines, people, n=6):
    ann = Principal(people["ann"][0])
    o = service.submit(ann, "stream.open", {"proof_revision_url": url(engines), "meta": "opened"})
    s = o.event["stream_id"]
    receipts = [o]
    for i in range(n):
        receipts.append(service.submit(ann, "task.open", {"stream_id": s, "task_id": U("t%d" % i), "meta": "m%d" % i}))
    assert all(isinstance(r, Accepted) for r in receipts)
    return s, receipts


def test_continuity_across_batches_and_concurrent_writers(service, engines, people):
    s, receipts = fill(service, engines, people, 1)
    rows = rows_of(service.store, s)
    assert [r.chain for r in receipts] == [h.hex() for h in chain.heads(s, rows)]
    assert service.head(s) == (len(rows), chain.heads(s, rows)[-1])
    ann = Principal(people["ann"][0])
    out = []
    ts = [threading.Thread(target=lambda i=i: out.append(service.submit(
        ann, "task.open", {"stream_id": s, "task_id": U("c%d" % i), "meta": "same"}))) for i in range(40)]
    [t.start() for t in ts]
    [t.join() for t in ts]
    rows = rows_of(service.store, s)
    assert len(rows) == 42 and chain.verify(s, rows).ok
    heads = chain.heads(s, rows)
    assert all(r.chain == heads[r.seq].hex() for r in out)


def test_salts_and_commitments(service, engines, people):
    s, _ = fill(service, engines, people, 0)
    ann = Principal(people["ann"][0])
    for k in ("x", "y"):
        service.submit(ann, "task.open", {"stream_id": s, "task_id": U(k), "meta": "the same meta"})
    service.submit(ann, "task.open", {"stream_id": s, "task_id": U("z")})          # no meta: a salt all the same
    stored = service.store.read_chained(s)
    salts = [r[3] for r in stored]
    assert all(len(x) == 16 for x in salts) and len(set(salts)) == len(salts)
    c1 = chain.redact(wire.loads(stored[1][1]), wire.loads(stored[1][2]), salts[1])[2]
    c2 = chain.redact(wire.loads(stored[2][1]), wire.loads(stored[2][2]), salts[2])[2]
    assert c1.startswith("sha256:") and c1 != c2
    assert chain.redact(wire.loads(stored[3][1]), wire.loads(stored[3][2]), salts[3])[2] is None


def test_legacy_rows_chain_on(service, engines, people):
    """Rows written before the chain (no salt, no head) are hashed with an empty salt; new rows chain on from there."""
    ann = people["ann"][0]
    s = U("legacy-stream")
    e = Engine(revision_map(engines)[engines["tasks"]])
    e.start()
    reqs = [{"actor_id": ann, "command": {"command": "stream.open", "proof_revision_url": url(engines),
             "meta": "old"}, "fresh": [s]},
            {"actor_id": ann, "command": {"command": "task.open", "stream_id": s, "task_id": U("old"),
             "meta": "old task"}, "fresh": []}]
    legacy = [(r, e.decide(r)["event"], "legacy-%d" % i) for i, r in enumerate(reqs)]
    e.stop()
    assert service.store.append_batch(s, 0, legacy)                             # without the chain's columns
    new = service.submit(Principal(ann), "task.open", {"stream_id": s, "task_id": U("new"), "meta": "new task"})
    rows = rows_of(service.store, s)
    assert rows[0].salt is None and rows[0].chain is None and rows[2].chain is not None
    heads = chain.heads(s, rows)
    assert new.chain == heads[2].hex() and chain.verify(s, rows).ok
    assert service.head(s) == (3, heads[2])
    assert service.chain_at(s, 1) == heads[1]


def mutate(rows, f):
    rows = copy.deepcopy(rows)
    f(rows)
    return rows


def test_verify_detects_changes(service, engines, people):
    s, receipts = fill(service, engines, people)
    rows = rows_of(service.store, s)
    assert chain.verify(s, rows).ok

    def req(rs): rs[3].request["command"]["task_id"] = U("other")
    def ev(rs): rs[3].event["actor_id"] = people["ben"][0]
    def meta(rs): rs[3].request["command"]["meta"] = "changed"; rs[3].event["meta"] = "changed"
    def reorder(rs): rs[3], rs[4] = rs[4], rs[3]
    def drop(rs): del rs[3]
    for f, why in ((req, "seq 3"), (ev, "seq 3"), (meta, "seq 3"), (reorder, "row 3"), (drop, "row 3")):
        r = chain.verify(s, mutate(rows, f))
        assert not r.ok and why in r.detail, (f.__name__, r.detail)
    # a held head catches a truncated tail, which the stored heads cannot
    last = len(rows) - 1
    assert chain.verify(s, rows[:-1]).ok
    r = chain.verify(s, rows[:-1], {last: receipts[-1].chain})
    assert not r.ok and "truncated" in r.detail
    r = chain.verify(s, rows[:-1], held_last=receipts[-1].chain)
    assert not r.ok
    assert chain.verify(s, rows, {2: receipts[2].chain}, receipts[-1].chain).ok


def test_erased_meta_still_chains(service, engines, people, tmp_path):
    s, _ = fill(service, engines, people, 3)
    stored = service.store.read_chained(s)
    lines = []
    for seq, r, e, salt, ch in stored:
        req, ev = wire.loads(r), wire.loads(e)
        row = {"stream_id": s, "seq": seq, "request": req, "event": ev, "meta_salt": salt.hex(), "chain": ch.hex()}
        if seq == 2:                                         # the meta of row 2 removed from storage
            row["meta_commitment"] = chain.redact(req, ev, salt)[2]
            req["command"]["meta"] = None                   # erased in place: the key keeps its position
            ev["meta"] = None
        lines.append(json.dumps(row))
    path = str(tmp_path / "rows.jsonl")
    open(path, "w").write("\n".join(lines) + "\n")
    rows = [chain.row_from_json(json.loads(l)) for l in lines]
    rep = chain.verify(s, rows)
    assert rep.ok and rep.erased == [2]
    p = subprocess.run([os.path.join(ROOT, "bin", "provenstream"), "verify", "--rows", path, "--engines",
                        engines["dir"], "--head", "%d:%s" % (len(rows) - 1, rows[-1].chain.hex())],
                       capture_output=True, text=True)
    assert p.returncode == 0, p.stdout + p.stderr
    assert "meta erased at seq 2" in p.stdout and "2 rows replay" in p.stdout
    p = subprocess.run([os.path.join(ROOT, "bin", "provenstream"), "verify", "--rows", path, "--engines",
                        engines["dir"], "--head", "%d:%s" % (len(rows), "00" * 32)], capture_output=True, text=True)
    assert p.returncode == 1 and "truncated" in p.stdout
