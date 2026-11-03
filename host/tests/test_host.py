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
