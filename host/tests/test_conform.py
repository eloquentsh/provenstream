# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The conformance suite (conformance/) and its runner (`provenstream conform`): the cases are what make_cases.py
writes and name every answer code and reason; every case passes on the three local carriers with the same bytes
(`--compare`); a wrong expectation fails, saying what was expected and what came; a host served apart passes as a
remote one, with the cases that need a host the runner made skipped and no token printed; and the pattern matcher's
rules, which decide all of it."""
import json, os, socket, subprocess, sys, time, urllib.request

import pytest

from conftest import ROOT

from provenstream import conform, protocol
from provenstream.conform import Mismatch, Result, match

BIN = os.path.join(ROOT, "bin", "provenstream")
CASES = os.path.join(ROOT, "conformance", "cases")


def clean_env():
    return {k: v for k, v in os.environ.items() if not k.startswith("PROVENSTREAM_")}


def conform_cli(*args):
    return subprocess.run([BIN, "conform"] + list(args), capture_output=True, text=True, env=clean_env(), timeout=900)


def all_cases():
    return [c for _, cases in conform.load_cases(CASES) for c in cases]


def test_cases_are_what_make_cases_writes():
    p = subprocess.run([sys.executable, os.path.join(ROOT, "conformance", "make_cases.py"), "--check"],
                       capture_output=True, text=True)
    assert p.returncode == 0, p.stderr


HOST_REASONS = {"stream_must_exist", "revision_must_be_installed", "repository_must_match_the_engine",
                "engine_must_implement_the_interface", "actor_id_must_match_the_token",
                "idempotency_key_must_match_its_request", "only_the_operator_can_reissue_a_principal"}
PROOF_RULES = {
    "revision_url_must_name_a_commit", "stream_must_be_open", "only_opener_can_close", "only_opener_can_append",
    "only_admins_can_invite", "principal_must_be_new", "only_admins_can_promote", "principal_must_be_invited",
    "principal_is_promoted_once", "only_admins_can_summon", "only_opener_can_open_tasks", "task_id_must_be_new",
    "parent_task_must_exist", "only_opener_can_assign", "task_must_exist", "task_is_assigned_once",
    "only_assignee_can_finish", "task_is_completed_once", "only_opener_can_approve", "task_must_be_completed",
    "task_is_approved_once", "completed_tasks_must_be_approved_before_close", "only_opener_can_create",
    "work_id_must_be_new", "work_must_exist", "work_is_assigned_once", "only_assignee_can_ask",
    "only_asked_preparers_can_reply", "only_assignee_can_decide", "work_must_be_undecided",
    "preparer_must_not_be_the_assignee", "preparer_is_asked_once", "preparer_replies_once", "work_is_decided_once"}


def test_every_answer_code_and_reason_is_asked_for():
    """Every code of the answer table, every reason the host gives a caller and every rule of the six proofs a host
    can be brought to (all but the two the host never lets a caller reach, since it mints every fresh id: a stream id
    taken, and the wrong count of minted ids), each by at least one case; and every proof theme is command sequences."""
    codes, reasons = set(), set()
    for c in all_cases():
        e = c["expect"]
        if "result" in e:
            codes.add("ok")
        else:
            codes.add(e["error"]["data"]["code"])
            assert e["error"]["data"]["code"] in protocol.ANSWERS                 # data.code on every error
            if "reason" in e["error"]["data"]:
                reasons.add(e["error"]["data"]["reason"])
    assert codes == set(protocol.ANSWERS)
    assert reasons >= HOST_REASONS | PROOF_RULES, sorted(HOST_REASONS | PROOF_RULES - reasons)
    themes = {t for t, _ in conform.load_cases(CASES)}
    assert themes == {"core", "log", "principals", "tasks", "work", "tower", "auth", "parse", "reads", "paging", "idempotency",
                      "actor", "discovery", "host", "errors"}
    for proof in ("core", "log", "principals", "tasks", "work", "tower"):
        cases = dict(conform.load_cases(CASES))[proof]
        seqs = {c["id"].split("/")[1] for c in cases}
        assert len(seqs) >= 10, proof
        assert all(c.get("proof") == proof for c in cases)
        assert sum(1 for c in cases if c.get("check") == "chain") == len(seqs)       # each read back, chain checked


def test_compare_every_local_carrier(engines):
    """In process, stdio and HTTP, at once: every case passes, with the same answer bytes up to what the patterns
    leave open, on SQLite."""
    p = conform_cli("--compare", "--engines", engines["dir"])
    n = len(all_cases())
    assert p.returncode == 0, p.stdout[-4000:] + p.stderr[-2000:]
    assert "%d cases on inprocess = stdio = http (compared, run in parallel), on sqlite: %d passed, 0 failed, " \
           "0 skipped" % (n, n) in p.stdout
    assert "FAIL" not in p.stdout and "incident" not in p.stderr


def test_compare_on_postgres(engines, dsn):
    """The same on a Postgres database (`--db`), shared by the three carriers' hosts."""
    p = conform_cli("--compare", "--engines", engines["dir"], "--db", dsn)
    n = len(all_cases())
    assert p.returncode == 0, p.stdout[-4000:] + p.stderr[-2000:]
    assert "(compared, run in parallel), on postgres: %d passed, 0 failed, 0 skipped" % n in p.stdout


def test_a_wrong_expectation_fails(engines, tmp_path):
    lines = open(os.path.join(CASES, "tasks.jsonl"), encoding="utf-8").read().splitlines()
    for i, text in enumerate(lines):
        c = json.loads(text)
        if c["id"] == "tasks/story/04-open-by-other":
            assert c["expect"]["error"]["data"]["reason"] == "only_opener_can_open_tasks"
            c["expect"]["error"]["data"]["reason"] = "task_id_must_be_new"          # the proof says otherwise
            lines[i] = json.dumps(c, separators=(",", ":"))
    (tmp_path / "tasks.jsonl").write_text("\n".join(lines) + "\n")
    for target in ("inprocess", "http"):
        p = conform_cli("--target", target, "--engines", engines["dir"], "--revision", engines["commit"],
                        "--cases", str(tmp_path))
        assert p.returncode == 1, p.stdout
        out = p.stdout.splitlines()
        k = out.index("FAIL  tasks/story/04-open-by-other")
        assert '"reason":"task_id_must_be_new"' in out[k + 2] and "expected:" in out[k + 2]
        assert '"reason":"only_opener_can_open_tasks"' in out[k + 3] and "got:" in out[k + 3]
        assert sum(1 for x in out if x.startswith("FAIL")) == 1 and out[-1] == "conform: FAIL"


def free_port():
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0))
        return s.getsockname()[1]


def test_a_remote_host(engines, tmp_path):
    """A host served apart, its principals issued by its operator: the remote run passes, skips what needs a host the
    runner made, prints no token, and refuses two roles that are one principal."""
    db = "sqlite:///" + str(tmp_path / "streams.db").lstrip("/")
    tokens, files = {}, {}
    for role in ("opener", "other", "third", "outsider"):
        tf = tmp_path / (role + ".token")
        got = json.loads(subprocess.run([BIN, "host", "principal", "create", "--db", db, "--token-file", str(tf)],
                                        capture_output=True, text=True, env=clean_env(), check=True).stdout)
        assert set(got) == {"principal_id"}
        tokens[role] = tf.read_text().strip()
        files[role] = role + ".token"
    (tmp_path / "tokens.json").write_text(json.dumps(files))
    port = free_port()
    server = subprocess.Popen([BIN, "serve", "--db", db, "--engines", engines["dir"], "--port", str(port)],
                              stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=clean_env())
    url = "http://127.0.0.1:%d" % port
    try:
        for _ in range(300):
            try:
                urllib.request.urlopen(url + "/healthz", timeout=1)
                break
            except OSError:
                time.sleep(0.1)
        rev_url = engines["urls"]["core"]
        p = conform_cli("--base-url", url, "--tokens", str(tmp_path / "tokens.json"), "--revision-url", rev_url)
        local_only = sum(1 for c in all_cases() if c.get("local_only"))
        assert p.returncode == 0, p.stdout[-4000:] + p.stderr
        assert "passed, 0 failed, %d skipped" % local_only in p.stdout
        assert not any(t in p.stdout + p.stderr for t in tokens.values())
        files["third"] = "outsider.token"                                          # two roles, one principal
        (tmp_path / "tokens.json").write_text(json.dumps(files))
        p = conform_cli("--base-url", url, "--tokens", str(tmp_path / "tokens.json"), "--revision-url", rev_url)
        assert p.returncode == 2 and "four distinct principals" in p.stderr
        assert not any(t in p.stdout + p.stderr for t in tokens.values())
        p = conform_cli("--base-url", url, "--revision-url", rev_url)
        assert p.returncode == 2 and "--tokens" in p.stderr
    finally:
        server.terminate()
        server.wait(30)


# -- the matcher ------------------------------------------------------------------------------------------------------

def test_match_binds_references_and_normalises():
    env = {"opener": "a"}
    got = {"seq": 0, "event": {"stream_id": "0193aaaa-0000-7000-8000-000000000000", "actor_id": "a"}, "chain": "f" * 64}
    p = {"seq": 0, "event": {"stream_id": "$uuid:s", "actor_id": "$opener"}, "chain": "$hex64:c"}
    assert match(p, got, env) == {"seq": 0, "event": {"stream_id": "$uuid:s", "actor_id": "$opener"},
                                  "chain": "$hex64:c"}
    assert env["s"] == got["event"]["stream_id"] and env["c"] == "f" * 64
    assert match("${opener}@x", "a@x", env) == "a@x"                                # a text with a bound value in it
    with pytest.raises(Mismatch):
        match("${opener}@x", "b@x", env)
    assert match({"x": "$s", "n": "$int", "t": "$string"}, {"x": env["s"], "n": 3, "t": "words"}, env) == \
        {"x": "$s", "n": 3, "t": "words"}                                         # $int, $string: compared as sent
    for p, a in [({"x": "$s"}, {"x": "other"}), ({"x": 1}, {"x": 1.0}), ({"x": 1}, {"x": True}),
                 ({"x": 1}, {"x": 1, "y": 2}), ({"x": 1, "y": 2}, {"x": 1}), ([1, 2], [1]), ("$nobody", "x"),
                 ({"x": "$uuid"}, {"x": "0193AAAA-0000-7000-8000-000000000000"}), ("$$lit", "$lit2")]:
        with pytest.raises(Mismatch):
            match(p, a, dict(env))
    assert match("$$lit", "$lit", {}) == "$lit"
    assert match({"$open": True, "x": 1}, {"x": 1, "y": 2}, {}) == {"x": 1, "y": 2}
    e = {}
    assert match({"$contains": [{"r": "$string:r", "up": "$any"}, 7]}, [3, 7, {"r": "a", "up": False}], e) == \
        [3, 7, {"r": "$string:r", "up": "$any"}] and e == {"r": "a"}
    with pytest.raises(Mismatch):
        match({"$contains": [7, 7]}, [7], {})                                     # one element, one match


def test_compare_needs_the_same_bytes():
    ok = lambda n, raw=b'{"a":1}': Result("t/c", "PASS", normal=n, raw=raw)
    assert conform.compare({"x": [ok('{"a":1}')], "y": [ok('{"a":1}')]})[0].status == "PASS"
    r = conform.compare({"x": [ok('{"a":1}')], "y": [ok('{"a":2}', b'{"a":2}')]})[0]
    assert r.status == "FAIL" and "carriers differ" in r.note
    r = conform.compare({"x": [ok('{"a":1}', b'{"a": 1}')], "y": [ok('{"a":1}')]})[0]
    assert r.status == "FAIL" and "canonical" in r.note
    r = conform.compare({"x": [ok('{"a":1}')], "y": [Result("t/c", "SKIP", "no token")]})[0]
    assert r.status == "PASS" and "skipped on y" in r.note


def test_the_chain_check():
    """`"check": "chain"`: a stream.rows answer whose rows do not chain from the genesis fails, whatever it matched."""
    from provenstream import chain, wire
    s = "0193aaaa-0000-7000-8000-000000000000"
    req, ev = {"actor_id": s, "command": {"command": "stream.open"}, "fresh": [s]}, {"event": "stream.opened"}
    salt = chain.new_salt()
    r, e, _ = chain.redact(req, ev, salt)
    head = chain.link(chain.genesis(s), 0, r, e)
    row = {"seq": 0, "request": wire.dumps(req), "event": wire.dumps(ev), "meta_salt": salt.hex(), "chain": head.hex()}
    assert conform.chain_problem(s, {"rows": [row]}) is None
    assert conform.chain_problem(s, {"rows": [dict(row, chain="00" * 32)]})
    assert conform.chain_problem(s, {"rows": [dict(row, event=wire.dumps({"event": "x"}))]})
    assert conform.chain_problem(s, {"rows": [dict(row, seq=1)]}) == "the rows are not every row from seq 0"
    assert conform.chain_problem(None, {"rows": []})
