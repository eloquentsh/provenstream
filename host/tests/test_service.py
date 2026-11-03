# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The service's environment, where no conformance sequence reaches: concurrent writers on one stream and two hosts on
one database (one sequence, compare-and-set), engines stopped when idle and restarted, eviction, snapshots re-folded
before use, the usage counters' values, forged rows found by replay, and streams of a revision this host does not
serve. What a caller sees of a stream (every rule, every refusal, idempotency, actor_id, references) is the
conformance suite's (conformance/: core, log, principals, tasks, tower, idempotency, actor, errors)."""
import threading, time

import pytest

from conftest import U, raw_sql, revision_map

from provenstream.service import Accepted, OtherRevision, Principal, Rejected, Service


def P(people, name):
    return Principal(people[name][0])


def open_stream(service, engines, people, key="tasks", who="ann"):
    a = service.submit(P(people, who), "stream.open", {"proof_revision_url": engines["urls"][key]})
    assert isinstance(a, Accepted), a
    return a.event["stream_id"]


def test_concurrent_writers_one_sequence(service, engines, people):
    s = open_stream(service, engines, people)
    ann = P(people, "ann")
    out = []

    def go(i):
        out.append(service.submit(ann, "task.open", {"stream_id": s, "task_id": U("w%d" % i)}))
    ts = [threading.Thread(target=go, args=(i,)) for i in range(40)]
    [t.start() for t in ts]
    [t.join() for t in ts]
    assert all(isinstance(o, Accepted) for o in out)
    assert sorted(o.seq for o in out) == list(range(1, 41))
    assert [r[0] for r in service.store.read(s)] == list(range(41))


def test_two_hosts_on_one_database(store, store_target, engines, people):
    from provenstream.store import open_store
    store2 = open_store(store_target)
    a, b = Service(store, revision_map(engines)), Service(store2, revision_map(engines))
    try:
        s = open_stream(a, engines, people)
        ann = P(people, "ann")
        out = []
        ts = [threading.Thread(target=lambda i=i: out.append((a if i % 2 else b).submit(
            ann, "task.open", {"stream_id": s, "task_id": U("x%d" % i)}))) for i in range(20)]
        [t.start() for t in ts]
        [t.join() for t in ts]
        assert all(isinstance(o, Accepted) for o in out)
        assert [r[0] for r in store.read(s)] == list(range(21))
        assert a.check_all()["bad_streams"] == []
    finally:
        a.close(); b.close(); store2.close()


def test_idle_engines_stop_and_restart(store, engines, people):
    svc = Service(store, revision_map(engines), idle_timeout=0.3)
    try:
        s = open_stream(svc, engines, people)
        assert svc.running()[engines["tasks"]]
        deadline = time.time() + 10
        while svc.running()[engines["tasks"]] and time.time() < deadline:
            time.sleep(0.1)
        assert not svc.running()[engines["tasks"]]             # no process for an idle revision
        out = svc.submit(P(people, "ann"), "task.open", {"stream_id": s, "task_id": U("w")})
        assert isinstance(out, Accepted) and out.seq == 1       # restarted, the stream reloaded from the store
        cpu = [r for r in svc.usage_report("revision") if r["key"] == engines["tasks"]]
        assert cpu and cpu[0]["cpu_ms"] >= 0
    finally:
        svc.close()


def test_eviction_keeps_answers_right(store, engines, people):
    svc = Service(store, revision_map(engines), max_streams=1)
    try:
        s1 = open_stream(svc, engines, people)
        s2 = open_stream(svc, engines, people)
        assert list(svc.judges[engines["tasks"]].synced) == [s2]
        ann = P(people, "ann")
        assert isinstance(svc.submit(ann, "task.open", {"stream_id": s1, "task_id": U("a")}), Accepted)
        assert svc.submit(ann, "task.open", {"stream_id": s1, "task_id": U("a")}) == Rejected("task_id_must_be_new")
        assert isinstance(svc.submit(ann, "task.open", {"stream_id": s2, "task_id": U("a")}), Accepted)
    finally:
        svc.close()


def test_snapshots_are_refolded_before_use(service, engines, people):
    s = open_stream(service, engines, people)
    ann = P(people, "ann")
    for i in range(6):
        assert isinstance(service.submit(ann, "task.open", {"stream_id": s, "task_id": U("w%d" % i)}), Accepted)
    assert [k for k, _, _ in service.store.snapshots(s, engines["tasks"])] == [5]
    service.store._tx(lambda ex: ex("UPDATE snapshots SET state = %s", ('{"core":{},"layer":[]}',)))
    service._forget(s)
    service.judges[engines["tasks"]].verified.clear()
    assert service.read_stream(s)["tasks"] and service.store.snapshots(s, engines["tasks"]) == []


def test_usage_counters(service, engines, people):
    s = open_stream(service, engines, people)
    ann = P(people, "ann")
    service.submit(ann, "task.open", {"stream_id": s, "task_id": U("w")})
    service.submit(ann, "task.open", {"stream_id": s, "task_id": U("w")})          # refused: counted, not stored
    u = {r["key"]: r for r in service.usage_report("stream")}[s]
    assert (u["received"], u["accepted"], u["events"]) == (3, 2, 2)
    assert u["bytes_stored"] == service.store.stored_bytes(s) > 0 and u["engine_ms"] >= 0 and u["last_active"]


def test_forged_rows_are_found(service, engines, people, store_target):
    s = open_stream(service, engines, people)
    service.submit(P(people, "ann"), "task.open", {"stream_id": s, "task_id": U("w")})
    raw_sql(store_target, "UPDATE events SET event = replace(event, %s, %s) WHERE seq = 1",
            (people["ann"][0], people["dee"][0]), forge=True)
    assert service.check_all()["bad_streams"] == [s]


def test_other_revision_streams_are_not_judged(store, engines, people):
    full = revision_map(engines)
    svc = Service(store, full)
    s = open_stream(svc, engines, people, key="core")
    svc.close()
    only_tasks = Service(store, {engines["tasks"]: full[engines["tasks"]]})
    try:
        with pytest.raises(OtherRevision):
            only_tasks.read_stream(s)
        assert only_tasks.check_all()["other_revision"] == [s]
    finally:
        only_tasks.close()
