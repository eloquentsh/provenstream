# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The host's environment, where no conformance sequence reaches: the in-process helpers an embedder calls
(`Host.command`, `Host.query`, `Operator`), the operator's `principal.create` (in process only), and the HTTP carrier's
own route, /healthz. Everything a caller can send over a carrier (parsing, the answer table, reads, paging, discovery,
refusals, idempotency, actor_id, principal.create by a token's caller) is conformance/'s."""
import json

import pytest
from starlette.testclient import TestClient

from conftest import U

from provenstream import protocol
from provenstream.api import make_app
from provenstream.host import Host, HostError, Operator, Token


@pytest.fixture
def host(service):
    return Host(service)


def tok(people, name):
    return Token(people[name][1])


def req(method, params=None, rid=1):
    return {"jsonrpc": "2.0", "id": rid, "method": method, "params": params or {}}


def test_command_and_query_helpers(host, engines, people):
    """An embedder acts as any principal the store knows (`Operator(p)`), reads as no principal (`Operator(None)`), and
    gets each answer as a result or a `HostError` carrying it."""
    ann, ben = people["ann"][0], people["ben"][0]
    s = host.command("stream.open", auth=Operator(ann), proof_revision_url=engines["urls"]["tasks"])["event"]
    assert s["actor_id"] == ann and s["event"] == "stream.opened"
    s = s["stream_id"]
    assert host.query("stream.head", auth=Operator(None), stream_id=s)["length"] == 1
    with pytest.raises(HostError) as x:
        host.command("task.open", auth=Operator(ben), stream_id=s, task_id=U("w"))
    assert x.value.answer.code == "refused" and x.value.answer.data["reason"] == "only_opener_can_open_tasks"
    with pytest.raises(HostError) as x:
        host.command("task.open", auth=Operator(ann), stream_id=s, task_id=U("w"), actor_id=ben)
    assert x.value.answer.data["reason"] == "actor_id_must_match_the_token"
    assert host.command("task.open", auth=Operator(ann), stream_id=s, task_id=U("w"), actor_id=ann)["seq"] == 1
    with pytest.raises(HostError) as x:
        host.command("task.open", auth=Operator(None), stream_id=s, task_id=U("v"))     # acts as no one
    assert x.value.answer.code == "unauthorized"
    with pytest.raises(HostError) as x:
        host.query("task.open", auth=tok(people, "ann"), stream_id=s, task_id=U("w"))   # a command, not a query
    assert x.value.answer.code == "method_not_found"
    with pytest.raises(HostError) as x:
        host.query("stream.get", auth=tok(people, "ann"), stream_id=s, extra=1)
    assert x.value.answer.code == "invalid_params" and "extra" in x.value.answer.data["detail"]
    with pytest.raises(HostError) as x:
        host.query("whoami", auth=Operator(U("nobody")))
    assert x.value.answer.code == "invalid_params"
    with pytest.raises(TypeError):
        host.handle(req("whoami"), people["ann"][1])                      # auth is a Token or an Operator, never a str


def test_principal_create_by_the_operator(host, people):
    """The operator issues principals as no principal, and alone re-issues a token for an id the store holds none for
    (after an import); an id that holds one is refused."""
    got = host.command("principal.create", auth=Operator(None))
    assert set(got) == {"principal_id", "token"}
    assert host.query("whoami", auth=Token(got["token"])) == {"principal_id": got["principal_id"]}
    imported = U("imported")
    again = host.command("principal.create", auth=Operator(None), principal_id=imported)
    assert again["principal_id"] == imported and host.query("whoami", auth=Token(again["token"])) == \
        {"principal_id": imported}
    assert host.command("principal.create", auth=Operator(people["ann"][0]), principal_id=U("another"))["principal_id"] \
        == U("another")
    for p in (imported, people["ann"][0]):
        a = host.handle(req("principal.create", {"principal_id": p}), Operator(None))
        assert a.code == "refused" and a.data["reason"] == "principal_must_have_no_token", a
    a = host.handle(req("principal.create", {"principal_id": U("by-token")}), tok(people, "ann"))
    assert a.code == "refused" and a.data["reason"] == "only_the_operator_can_reissue_a_principal"
    for bad in ({"kind": "person"}, {"principal_id": "x"}):
        assert host.handle(req("principal.create", bad), Operator(None)).code == "invalid_params", bad


def test_http_carrier_and_healthz(host, people, monkeypatch):
    c = TestClient(make_app(host))
    r = c.post("/rpc", content=b"x" * (protocol.MAX_BODY + 1))
    assert r.status_code == 200 and r.json()["error"]["data"] == {
        "code": "invalid_request", "detail": "message over %d bytes" % protocol.MAX_BODY}
    r = c.post("/rpc", content=json.dumps(req("whoami", rid="a")),
               headers={"Authorization": "Bearer " + people["ann"][1]}).json()
    assert r == {"jsonrpc": "2.0", "id": "a", "result": {"principal_id": people["ann"][0]}}
    r = c.get("/healthz")
    assert r.status_code == 200 and r.json() == {"ok": True}

    def down():
        raise RuntimeError("could not connect to /var/run/postgresql")
    monkeypatch.setattr(host.store, "ping", down)
    r = c.get("/healthz")
    assert r.status_code == 503 and r.json() == {"ok": False}


def _events(host, auth, revision, **params):
    return host.query("revision.events", auth=auth, revision=revision, **params)


def test_revision_events_across_streams(host, engines, people):
    """`revision.events` answers the events of every stream of a revision in the host's append order, not another
    revision's, and `event` narrows it to one event name. A principal finds the events that name it across streams it
    was never told about: the asks of the revision, in one call, its own id among the preparers."""
    ann, ben, cy, dee = (people[n][0] for n in ("ann", "ben", "cy", "dee"))
    work, tasks = engines["work"], engines["tasks"]
    expected = []                                           # (stream_id, seq, event) in the order appended

    def send(who, method, **params):
        r = host.command(method, auth=Operator(who), **params)
        expected.append((r["event"]["stream_id"], r["seq"], r["event"]["event"]))
        return r["event"]
    streams = [send(ann, "stream.open", proof_revision_url=engines["urls"]["work"])["stream_id"] for _ in range(3)]
    t = send(ann, "stream.open", proof_revision_url=engines["urls"]["tasks"])["stream_id"]
    send(ann, "task.open", stream_id=t, task_id=U("task"))
    items = [U("w%d" % i) for i in range(3)]
    for s, w, assignee, preparer in zip(streams, items, (ann, ann, cy), (ben, ben, dee)):
        send(ann, "work.create", stream_id=s, work_id=w)
        send(ann, "work.assign", stream_id=s, work_id=w, assignee_id=assignee)
        send(assignee, "work.ask", stream_id=s, work_id=w, preparer_id=preparer, meta="please")
    of_work = [(s, seq, e) for s, seq, e in expected if s != t]
    assert len(expected) == 14 and len(of_work) == 12

    # ben's inbox: the asks of the revision, in append order, from streams it was never told of; two name it
    got = _events(host, tok(people, "ben"), work, event="work.asked")
    assert got["revision"] == work and got["next"] is None
    assert [(e["stream_id"], e["seq"], e["event"]) for e in got["events"]] == \
        [(s, seq, e) for s, seq, e in of_work if e == "work.asked"]
    mine = [e for e in got["events"] if e["preparer_id"] == ben]
    assert [e["stream_id"] for e in mine] == streams[:2] and all(e["meta"] == "please" for e in mine)
    for e in got["events"]:
        page = host.query("stream.events", auth=Operator(None), stream_id=e["stream_id"], **{"from": e["seq"], "limit": 1})
        assert page["events"][0] == e                        # the same event, seq and chain head as the stream says
    # the whole revision, in append order, without the tasks stream's events; the operator as no principal reads too
    whole = _events(host, Operator(None), work)
    assert [(e["stream_id"], e["seq"], e["event"]) for e in whole["events"]] == of_work and whole["next"] is None
    assert [e["work_id"] for e in _events(host, tok(people, "ann"), work, event="work.created")["events"]] == items
    assert _events(host, tok(people, "ann"), work, event="work.replied")["events"] == []
    # the tasks revision has its stream's events alone, and a served revision with no stream yet answers none
    assert [(e["stream_id"], e["event"]) for e in _events(host, tok(people, "ann"), tasks)["events"]] == \
        [(t, "stream.opened"), (t, "task.opened")]
    assert _events(host, tok(people, "ann"), engines["log"]) == {"revision": engines["log"], "events": [], "next": None}


def test_revision_events_pages_from_a_position(host, engines, people):
    """Paging with `next` walks every match once and ends with null, for the whole revision and for one event name; a
    page is at most `limit`; a position past the end answers an empty page; a stored `next` is where to poll from."""
    ann = people["ann"][0]
    work = engines["work"]
    streams = [host.command("stream.open", auth=Operator(ann), proof_revision_url=engines["urls"]["work"])["event"]["stream_id"]
               for _ in range(2)]
    for i in range(5):
        for s in streams:
            host.command("work.create", auth=Operator(ann), stream_id=s, work_id=U("p%d%s" % (i, s)))
    whole = _events(host, Operator(None), work)["events"]
    assert len(whole) == 12 and whole[0]["seq"] == 0 and whole[1]["seq"] == 0            # the two opens, then creates

    def walk(limit, **params):
        out, cursor, pages = [], 0, 0
        while True:
            page = _events(host, tok(people, "ben"), work, limit=limit, **dict(params, **{"from": cursor}))
            assert len(page["events"]) <= limit
            out += page["events"]
            pages += 1
            cursor = page["next"]
            if cursor is None:
                return out, pages
            assert isinstance(cursor, int)
    for limit, pages in ((5, 3), (12, 1), (1, 12), (1000, 1)):
        got, n = walk(limit)
        assert got == whole and n == pages, limit
    created = [e for e in whole if e["event"] == "work.created"]
    got, n = walk(3, event="work.created")
    assert got == created and n == 4
    last = _events(host, Operator(None), work, limit=11)["next"]
    rest = _events(host, Operator(None), work, **{"from": last})
    assert rest["events"] == whole[11:] and rest["next"] is None
    assert _events(host, Operator(None), work, **{"from": last + 10 ** 6}) == {"revision": work, "events": [], "next": None}
    # a position is where to poll from: nothing new, an empty page; something new, just that
    end = _events(host, Operator(None), work, limit=12)
    assert end["events"] == whole and end["next"] is None
    before = [e for e in whole if e["stream_id"] == streams[1]][-1]
    host.command("work.create", auth=Operator(ann), stream_id=streams[1], work_id=U("late"))
    again = _events(host, Operator(None), work, limit=12)
    assert again["events"] == whole and again["next"] is not None
    new = _events(host, Operator(None), work, **{"from": again["next"]})
    assert [(e["stream_id"], e["seq"], e["work_id"]) for e in new["events"]] == [(streams[1], before["seq"] + 1, U("late"))]
    assert new["next"] is None


def test_revision_events_refusals(host, engines, people):
    """A revision with no engine here is refused `revision_must_be_installed`; a malformed revision, event name,
    position or limit is invalid_params; a caller with a bad token, or none, is unauthorized."""
    work = engines["work"]
    for rev in ("0" * 40, engines["commit"] + "/examples/nothing"):
        a = host.handle(req("revision.events", {"revision": rev}), tok(people, "ann"))
        assert a.code == "refused" and a.data["reason"] == "revision_must_be_installed", a
    for bad in ({"event": "asked"}, {"event": "Work.Asked"}, {"from": "3"}, {"from": -1}, {"from": 1.5},
                {"from": True}, {"limit": 0}, {"limit": 1001}, {"stream_id": U("s")}, {"where": {"x": 1}}):
        a = host.handle(req("revision.events", dict({"revision": work}, **bad)), tok(people, "ann"))
        assert a.code == "invalid_params", (bad, a)
    for bad in ("abc1234", engines["urls"]["work"], engines["commit"] + "/a//b", ""):
        a = host.handle(req("revision.events", {"revision": bad}), tok(people, "ann"))
        assert a.code == "invalid_params", (bad, a)
    assert host.handle(req("revision.events", {"revision": work}), Token("ls_not-a-token")).code == "unauthorized"
    assert host.handle(req("revision.events", {"revision": work}), Token(None)).code == "unauthorized"
