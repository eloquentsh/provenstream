# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Every proof inherits from the core's, and its engine implements the stream interface. A valid proof (it builds and
proves its theorems, and its engine passes its self-test and describes itself) that does not inherit is refused when it
is built (`project.inherits`), and an engine that does not implement the interface when it is installed and by a host
asked to open a stream on it (`interface.py`). The proofs are `tests/not-the-interface/`: `norules` describes the
core's commands but applies none of its rules; `counter` is a command and event stream of its own; `otherbase` is the
tasks layer on a copy of the core's base with `only_opener_can_close` taken out, which its description shows and the
core's recorded sessions (a close by someone other than the opener) find. The core, the tasks layer and the tower (a
layer on a layer) pass both."""
import json, os, shutil, subprocess
from unittest import mock

import pytest

from conftest import ROOT, U

from provenstream import interface
from provenstream.build import BuildFailed, build_engine, install
from provenstream.revisions import add_engine, engine_dir, load_map
from provenstream.service import Principal, Rejected, Service

# Each proof that does not inherit from the core's, and why: in its source (the build), in its engine (the interface).
NOT_INHERITED = {
    "norules": "main is not Provenstream.Engine.Layered.mainAt of a layer",
    "counter": "main is not Provenstream.Engine.Layered.mainAt of a layer",
    "otherbase": "OtherBase.tasks: its base is OtherBase.looseBase, which is not the core's",
}
NOT_THE_INTERFACE = {
    "norules": "core-rules line 1: the core answers {\"stream_id\":\"50000000-0000-7000-8000-000000000001\","
               "\"reason\":\"stream_must_exist\"",
    "counter": "it does not describe the core's stream.open (it describes counter.add)",
    "otherbase": "it describes stream.close otherwise than the core does",
}
LINES = 89                                         # the lines of the core's sessions (interface/core-*.in.jsonl)


def build(engines, name, out, say=lambda *a: None, package=None):
    return build_engine(engines["repo"], engines["commit"], out, package=package or "tests/not-the-interface/" + name,
                        repo_url=engines["url"], reuse_lake=ROOT, say=say)


@pytest.fixture(scope="module")
def built(engines, tmp_path_factory):
    """Each proof built with both checks left out (as a provenstream from before them would have built it): a build
    directory with its engine and manifest, {name: directory}."""
    out = {}
    base = tmp_path_factory.mktemp("not-the-interface")
    with mock.patch.object(interface, "check_engine", lambda path, timeout=30.0: {"lines": 0, "compared": 0,
                                                                                  "guarded": []}), \
            mock.patch("provenstream.project.inherits", lambda project, cfg: "inherits: not checked"):
        for name in NOT_INHERITED:
            build(engines, name, str(base / name))
            out[name] = str(base / name)
    return out


@pytest.mark.parametrize("name", sorted(NOT_INHERITED))
def test_its_proof_builds_and_describes_itself(built, name):
    """The control: each is a proof that builds, passes its own self-test and reports its revision, so only the
    checks tell it from a proof on the core's."""
    engine = os.path.join(built[name], "engine")
    assert subprocess.run([engine, "--self-test"], capture_output=True).returncode == 0
    desc = json.loads(subprocess.run([engine, "--describe"], capture_output=True, text=True).stdout)
    with open(os.path.join(built[name], "PROVENANCE.json"), encoding="utf-8") as f:
        m = json.load(f)
    assert (desc["revision"], desc["package"]) == (m["commit"], m["package"]) == \
        (m["commit"], "tests/not-the-interface/" + name)


@pytest.mark.parametrize("name", sorted(NOT_INHERITED))
def test_build_refuses_a_proof_that_does_not_inherit(engines, tmp_path, name):
    with pytest.raises(BuildFailed) as x:
        build(engines, name, str(tmp_path / "out"))
    assert "the engine does not inherit from the core's proof: " + NOT_INHERITED[name] in str(x.value), str(x.value)
    assert not os.path.exists(tmp_path / "out")


@pytest.mark.parametrize("name", sorted(NOT_THE_INTERFACE))
def test_build_finds_the_interface_mismatch_too(engines, tmp_path, name):
    """With the source check left out, the engine's description or answers still give it away."""
    with mock.patch("provenstream.project.inherits", lambda project, cfg: "inherits: not checked"):
        with pytest.raises(BuildFailed) as x:
            build(engines, name, str(tmp_path / "out"))
    assert "does not implement the stream interface" in str(x.value), str(x.value)
    assert NOT_THE_INTERFACE[name] in str(x.value), str(x.value)


def test_the_sessions_find_otherbase_without_its_description(built):
    """Were `otherbase` to describe `stream.close` as the core does, the recorded close by someone other than the
    opener (refused `only_opener_can_close` by the core) would still give it away."""
    with mock.patch.object(interface, "describe_mismatch", lambda desc: None):
        with pytest.raises(interface.InterfaceMismatch) as x:
            interface.check_engine(os.path.join(built["otherbase"], "engine"))
    assert "core-rules line 24: the core answers" in str(x.value) and "only_opener_can_close" in str(x.value), \
        str(x.value)


@pytest.mark.parametrize("name", sorted(NOT_THE_INTERFACE))
def test_install_finds_the_mismatch(built, tmp_path, name):
    edir = str(tmp_path / "engines")
    with pytest.raises(BuildFailed) as x:
        install(built[name], edir, say=lambda *a: None)
    assert "does not implement the stream interface" in str(x.value), str(x.value)
    assert NOT_THE_INTERFACE[name] in str(x.value), str(x.value)
    assert load_map(os.path.join(edir, "revisions.json")) == {}


@pytest.mark.parametrize("name", sorted(NOT_THE_INTERFACE))
def test_a_host_opens_no_stream_on_it(built, engines, store, tmp_path, name):
    """An engine in a host's engines directory without `install` (copied in, or installed before the check): a
    `stream.open` naming its revision is refused with the host's engine_must_implement_the_interface, and nothing is
    stored; an engine that implements the interface, beside it (another package of the same commit), still opens
    streams."""
    edir = str(tmp_path / "engines")
    rel = engine_dir(engines["core"])
    os.makedirs(os.path.join(edir, rel))
    shutil.copy2(os.path.join(built[name], "engine"), os.path.join(edir, rel, "engine"))
    add_engine(os.path.join(edir, "revisions.json"), engines["core"], rel + "/engine")
    rmap = load_map(os.path.join(edir, "revisions.json"))
    rmap[engines["tasks"]] = load_map(os.path.join(engines["dir"], "revisions.json"))[engines["tasks"]]
    ann = U("ann")
    store.create_principal(ann)
    svc = Service(store, rmap)
    try:
        for _ in range(2):                                  # the second answer is the host's record of the first check
            out = svc.submit(Principal(ann), "stream.open", {"proof_revision_url": engines["urls"]["core"]})
            assert out == Rejected("engine_must_implement_the_interface"), out
        assert NOT_THE_INTERFACE[name] in svc.judges[engines["core"]].interface
        assert store.streams() == [] and store.count() == 0
        ok = svc.submit(Principal(ann), "stream.open", {"proof_revision_url": engines["urls"]["tasks"]})
        assert ok.event["event"] == "stream.opened", ok
    finally:
        svc.close()


@pytest.mark.parametrize("key", ["core", "log", "principals", "tasks", "work", "tower"])
def test_stream_engines_implement_it(engines, key):
    """The core's engine and a layer's answer every recorded line as the core does: nothing refused more, nothing
    skipped."""
    command = load_map(os.path.join(engines["dir"], "revisions.json"))[engines[key]]
    report = interface.check(command)
    assert report == {"lines": LINES, "compared": LINES, "guarded": []}, report


def test_the_tower_builds_through_both(engines, tmp_path):
    """A layer on a layer (tests/tower: reviews on tasks on the core) inherits and implements the interface. Its
    guard on `stream.close` (no close while a completed task awaits approval) is described after the core's rules and
    refuses no line of the core's sessions."""
    said = []
    m = build(engines, "tower", str(tmp_path / "tower"), say=said.append, package="tests/tower")
    assert "inherits: main serves [Tower.reviews], on the core's proof" in said, said
    assert "interface: the core's sessions, %d of %d lines as the core answers them" % (LINES, LINES) in said, said
    assert [c["name"] for c in m["schema"]["commands"]][-1] == "review.approve"


def test_a_layer_may_refuse_more_but_no_core_refusal_changes():
    s, a = "50000000-0000-7000-8000-000000000001", U("ann")
    req = {"actor_id": a, "command": {"command": "stream.close", "stream_id": s}, "fresh": []}
    accepted = {"accept": True, "event": {"event": "stream.closed", "stream_id": s, "actor_id": a, "meta": None},
                "stream_id": s, "at": 3}
    refused = lambda r, at=3: {"accept": False, "reason": r, "stream_id": s, "at": at}
    assert interface.judge(req, accepted, accepted) == "same"
    assert interface.judge(req, accepted, refused("a_layer_guard")) == "guarded"
    assert interface.judge(req, accepted, refused("a_layer_guard", at=2)) == "mismatch"
    assert interface.judge(req, refused("only_opener_can_close"), refused("only_opener_can_close")) == "same"
    assert interface.judge(req, refused("only_opener_can_close"), refused("a_layer_guard")) == "mismatch"
    assert interface.judge(req, refused("only_opener_can_close"), accepted) == "mismatch"
    view = {"stream_id": s, "opener_id": a, "proof_revision_url": "u", "closed": False}
    assert interface.judge({"query": "stream", "stream_id": s}, view, dict(view, tasks=[])) == "same"
    assert interface.judge({"query": "stream", "stream_id": s}, view, dict(view, opener_id=U("ben"))) == "mismatch"


def test_a_layer_describes_the_core_commands_as_the_core_does():
    """The core's two commands, exactly, but a layer's guard on one may add its rule after the core's."""
    desc = lambda commands, protocol=2: {"protocol": protocol, "schema": {"commands": commands}}
    core = interface.base_schema()
    assert [c["name"] for c in core] == ["stream.open", "stream.close"]
    assert interface.describe_mismatch(desc(core)) is None
    close = next(c for c in core if c["name"] == "stream.close")
    guarded = [c if c is not close else dict(close, rules=close["rules"] + ["a_guard"]) for c in core]
    assert interface.describe_mismatch(desc(guarded + [{"name": "task.open"}])) is None
    for other in (dict(close, rules=close["rules"][:-1]), dict(close, rules=["a_guard"] + close["rules"]),
                  dict(close, who="anyone"), dict(close, fresh=1), dict(close, params=close["params"][:1]),
                  dict(close, event=dict(close["event"], name="stream.close"))):
        changed = [c if c is not close else other for c in core]
        assert interface.describe_mismatch(desc(changed)) == "it describes stream.close otherwise than the core does"
    assert interface.describe_mismatch(desc(core, 1)) == "it speaks engine protocol 1, not 2"
    assert interface.describe_mismatch({"schema": {"commands": core}}) == "it speaks engine protocol (none), not 2"


def test_the_sessions_are_the_corpus():
    """The check's sessions are the sealed corpus's core sessions, byte for byte (the host's package carries copies:
    an installed host has no checkout)."""
    for name in interface.SESSIONS:
        for ext in (".in.jsonl", ".out.jsonl"):
            with open(os.path.join(ROOT, "corpus", "sessions", name + ext), "rb") as a, \
                    open(os.path.join(interface.HERE, name + ext), "rb") as b:
                assert a.read() == b.read(), name + ext


def test_the_host_reads_revision_urls_as_the_core_does():
    """Every stream.open of the sealed corpus: the host's reading of its URL (`revisions.parse_url`) accepts it exactly
    when the core's rule does (`revision_url_must_name_a_commit`, Lean's validRevisionUrl), so the host's refusal of a
    URL it cannot route is the core's own."""
    from provenstream import wire
    from provenstream.revisions import parse_url
    seen = {True: 0, False: 0}
    sessions = os.path.join(ROOT, "corpus", "sessions")
    for name in sorted(f[:-len(".in.jsonl")] for f in os.listdir(sessions) if f.endswith(".in.jsonl")):
        ins = [l for l in open(os.path.join(sessions, name + ".in.jsonl"), encoding="utf-8") if l.strip()]
        outs = [l for l in open(os.path.join(sessions, name + ".out.jsonl"), encoding="utf-8") if l.strip()][1:]
        for line, ans in zip(ins, outs):
            try:
                req, a = wire.loads(line), wire.loads(ans)
            except wire.BadJson:
                continue
            cmd = req.get("command") if isinstance(req, dict) else None
            if not (isinstance(cmd, dict) and cmd.get("command") == "stream.open" and isinstance(a, dict)
                    and "accept" in a and isinstance(cmd.get("proof_revision_url"), str)):
                continue
            if a["accept"] is False and a["reason"] != "revision_url_must_name_a_commit":
                continue                                         # refused by a rule before it
            core_ok = a["accept"] is True
            assert (parse_url(cmd["proof_revision_url"]) is not None) == core_ok, (name, cmd["proof_revision_url"])
            seen[core_ok] += 1
    assert seen[True] >= 3 and seen[False] >= 10, seen
