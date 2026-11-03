# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
import json, os, sys

from conftest import U

import pytest

from provenstream.engine import Engine, EngineFailure
from provenstream.schema import commands_of


def engine_of(engines, proof):
    from provenstream.revisions import engine_dir
    return os.path.join(engines["dir"], engine_dir(engines[proof]), "engine")


def test_engines_describe_themselves(engines):
    """Each of the six engines of one commit reports that commit and its own package, describes the core's two
    commands and its layer's, and the manifest beside it says the same."""
    for proof, names in (("core", set()), ("log", {"log.append"}),
                         ("principals", {"principal.invite", "principal.promote", "principal.summon"}),
                         ("tasks", {"task.open", "task.assign", "task.complete"}),
                         ("work", {"work.create", "work.assign", "work.ask", "work.reply", "work.complete",
                                   "work.cancel"}),
                         ("tower", {"task.open", "review.approve"})):
        e = Engine([engine_of(engines, proof)])
        e.start()
        try:
            d = e.describe()
            assert d["revision"] == engines["commit"] and d["protocol"] == 2
            assert e.revision_key() == engines[proof]
            cmds = commands_of(d)
            assert {"stream.open", "stream.close"} | names <= set(cmds)
            assert cmds["stream.open"].fresh == 1 and cmds["stream.open"].minted == ("stream_id",)
            assert cmds["stream.close"].fresh == 0 and cmds["stream.close"].stream == "stream_id"
            assert cmds["stream.close"].rules[:3] == ("stream_must_exist", "stream_must_be_open",
                                                      "only_opener_can_close")
            # the description is the manifest's, and the schema query answers the same schema
            prov = json.load(open(os.path.join(os.path.dirname(engine_of(engines, proof)), "PROVENANCE.json")))
            assert prov["schema"] == d["schema"] and prov["revision"] == engines[proof]
            assert prov["proof_url"] == engines["urls"][proof]
            assert e.query({"query": "schema"}) == d["schema"]
        finally:
            e.stop()
        assert e.cpu_seconds() > 0          # measured from the reaped process


def test_engine_decides_and_reports_cpu(engines):
    e = Engine([engine_of(engines, "core")])
    e.start()
    a = e.decide({"actor_id": U("ann"), "command": {"command": "stream.open",
                                                    "proof_revision_url": engines["urls"]["core"]},
                  "fresh": [U("s")]})
    assert a["accept"] and a["at"] == 0 and a["event"]["actor_id"] == U("ann")
    r = e.decide({"actor_id": U("dee"), "command": {"command": "stream.close", "stream_id": U("s")}, "fresh": []})
    assert r == {"accept": False, "reason": "only_opener_can_close", "stream_id": U("s"), "at": 1}
    assert e.cpu_seconds() >= 0
    e.stop()
    assert not e.alive()


ENV_PROBE = r'''
import json, os, sys
print(json.dumps({"ready": True}), flush=True)
for line in sys.stdin:
    print(json.dumps(dict(os.environ)), flush=True)
'''


def test_engines_get_a_clean_environment(tmp_path, monkeypatch):
    """An engine is started with PATH and LEAN_ABORT_ON_PANIC only: nothing of the host's own settings reaches it."""
    probe = tmp_path / "probe.py"
    probe.write_text(ENV_PROBE)
    for k, v in (("PROVENSTREAM_DATABASE_URL", "postgresql://u:secret@db/x"), ("PGPASSWORD", "secret"),
                 ("PGHOST", "db"), ("PROVENSTREAM_TOKEN", "ps_secret"), ("AWS_SECRET_ACCESS_KEY", "secret")):
        monkeypatch.setenv(k, v)
    e = Engine([sys.executable, "-I", str(probe)])
    e.start()
    try:
        env = e.query({"query": "env"})
    finally:
        e.stop()
    assert env["LEAN_ABORT_ON_PANIC"] == "1" and env["PATH"] == os.environ["PATH"]
    assert "secret" not in json.dumps(env)
    # what the platform's process start may add (macOS sets __CF_USER_TEXT_ENCODING for any process) aside, nothing else
    assert {k for k in env if not k.startswith("__")} <= {"PATH", "LEAN_ABORT_ON_PANIC", "LC_CTYPE"}


def test_a_missing_engine_is_an_engine_failure(tmp_path):
    """An engine file that is not there (or cannot be run) does not start, like an engine that exits: EngineFailure,
    which the service answers as unavailable, rather than an OSError that escapes it (found by the conformance suite:
    one missing engine failed the whole of rpc.discover)."""
    for command in ([str(tmp_path / "missing" / "engine")], [str(tmp_path)]):
        e = Engine(command)
        with pytest.raises(EngineFailure, match="did not start"):
            e.start()
        assert not e.alive() and "did not start" in e.failed
