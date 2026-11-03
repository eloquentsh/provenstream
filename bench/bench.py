#!/usr/bin/env python3
# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Measure what a stream costs to run, on this machine. Nothing here is an estimate unless it says so.

    python3 bench/bench.py [--n 2000] [--fresh-build] [--out bench/results/NAME.json]

It builds the core's engine (the root package) and the tasks engine (the package `examples/tasks`) from a throwaway
commit of this checkout (the real pipeline, `provenstream.build`: a revision is a commit and a package path;
`--fresh-build` without Lake's caches, to time a cold build), starts a throwaway Postgres (scripts/pgtmp.py), and
measures, speaking engine protocol 2 (`PROTOCOL.md`) and the host's service API as it is (`actor_id`, no kinds, a
principal issued by `create_principal`):

- the engine alone: process start to ready; decisions per second (one stream, `task.open`, piped); stored rows
  replayed per second through the fast path (`sync`) and through the audit path (`check`); the engine's CPU seconds
  and peak resident memory (from the reaped process's resource usage); the binary's size;
- the host (the service, in process, no HTTP): accepted commands per second on one stream from one writer and from 32
  writers (group commit), and across 64 streams from 32 writers; stored bytes per event (exact, from Postgres: the
  request and event text, and separately the chain's salt and head); the
  engine's measured CPU milliseconds per 1000 commands; the host process's own CPU per 1000 commands.
"""
from __future__ import annotations
import argparse, json, os, platform, resource, shutil, subprocess, sys, tempfile, threading, time, uuid

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "host"))
sys.path.insert(0, os.path.join(ROOT, "scripts"))

from provenstream import wire  # noqa: E402
from provenstream.build import build_engine  # noqa: E402
from provenstream.revisions import revision_key, revision_url  # noqa: E402

URL = "https://example.org/provenstream-bench"
TASKS = "examples/tasks"                        # the package of the tasks example, in the repository


def U(name: str) -> str:
    return str(uuid.uuid5(uuid.NAMESPACE_URL, "bench:" + name))


def git(repo, *args):
    return subprocess.run(["git", "-C", repo, "-c", "user.name=bench", "-c", "user.email=bench@example.invalid"]
                          + list(args), check=True, capture_output=True, text=True).stdout.strip()


def build(tmp: str, fresh: bool):
    repo = os.path.join(tmp, "repo")
    subprocess.run(["rsync", "-a", "--exclude", ".lake", "--exclude", ".git", "--exclude", "__pycache__",
                    ROOT + "/", repo + "/"], check=True)
    subprocess.run(["git", "init", "-q", repo], check=True)
    git(repo, "add", "-A")
    git(repo, "commit", "-qm", "bench")
    c = git(repo, "rev-parse", "HEAD")
    quiet = lambda *a: None
    t0 = time.time()
    core = build_engine(repo, c, os.path.join(tmp, "core"), ".", URL, None if fresh else ROOT, say=quiet)
    t1 = time.time()
    layer = build_engine(repo, c, os.path.join(tmp, "tasks"), TASKS, URL, None if fresh else ROOT, say=quiet)
    t2 = time.time()
    return c, core, layer, {"core_build_s": round(t1 - t0, 1), "tasks_build_s": round(t2 - t1, 1),
                           "lake_cache": "none (cold)" if fresh else "reused from the checkout"}


def pipe(engine: str, lines):
    """Run an engine over lines; answer (wall seconds after ready, output lines, CPU seconds, peak RSS bytes)."""
    p = subprocess.Popen([engine], stdin=subprocess.PIPE, stdout=subprocess.PIPE, text=True)
    t_start = time.time()
    ready = p.stdout.readline()
    t_ready = time.time()
    assert json.loads(ready) == {"ready": True}
    out = []

    def feed():
        for l in lines:
            p.stdin.write(l + "\n")
        p.stdin.close()
    th = threading.Thread(target=feed)
    th.start()
    for _ in lines:
        out.append(p.stdout.readline())
    t_end = time.time()
    th.join()
    _, status, ru = os.wait4(p.pid, 0)
    rss = ru.ru_maxrss if sys.platform == "darwin" else ru.ru_maxrss * 1024
    return t_ready - t_start, t_end - t_ready, out, ru.ru_utime + ru.ru_stime, rss


def engine_bench(commit: str, engine: str, n: int) -> dict:
    s, ann = U("s"), U("ann")
    url = revision_url(URL, commit, TASKS)
    reqs = [{"actor_id": ann, "command": {"command": "stream.open", "proof_revision_url": url}, "fresh": [s]}]
    reqs += [{"actor_id": ann, "command": {"command": "task.open", "stream_id": s, "task_id": U("w%d" % i)},
              "fresh": []} for i in range(n)]
    lines = [wire.dumps(r) for r in reqs]
    startup, wall, out, cpu, rss = pipe(engine, lines)
    answers = [json.loads(l) for l in out]
    assert all(a.get("accept") for a in answers), answers[:3]
    rows = [{"request": r, "event": a["event"]} for r, a in zip(reqs, answers)]
    sync_line = wire.dumps({"sync": {"stream_id": s, "from": 0, "rows": rows}})
    _, sync_wall, sync_out, sync_cpu, _ = pipe(engine, [sync_line])
    assert json.loads(sync_out[0]).get("length") == len(rows), sync_out[0][:200]
    check_line = wire.dumps({"check": {"stream_id": s, "rows": rows}})
    _, check_wall, check_out, check_cpu, _ = pipe(engine, [check_line])
    assert json.loads(check_out[0]).get("length") == len(rows), check_out[0][:200]
    return {"startup_to_ready_ms": round(startup * 1000, 1),
            "decisions": len(lines), "decisions_per_s": round(len(lines) / wall),
            "decide_cpu_s": round(cpu, 3), "decide_peak_rss_mib": round(rss / 2 ** 20, 1),
            "sync_rows_per_s": round(len(rows) / sync_wall), "check_rows_per_s": round(len(rows) / check_wall),
            "binary_bytes": os.path.getsize(engine)}


def host_bench(commit: str, engines_dir: str, n: int) -> dict:
    import pgtmp
    from provenstream.revisions import load_map
    from provenstream.service import Accepted, Principal, Service
    from provenstream.store import open_store
    data = tempfile.mkdtemp(prefix="bench-pg-")
    cluster = pgtmp.start(data)
    try:
        store = open_store(pgtmp.create_db(cluster))
        ann = U("ann")
        store.create_principal(ann)                     # issues a token, which the bench never reads
        svc = Service(store, load_map(os.path.join(engines_dir, "revisions.json")), snapshot_every=1000)
        caller = Principal(ann)
        url = revision_url(URL, commit, TASKS)
        key = revision_key(commit, TASKS)
        out = {}

        def opened():
            a = svc.submit(caller, "stream.open", {"proof_revision_url": url})
            assert isinstance(a, Accepted), a
            return a.event["stream_id"]

        def run(label, streams, writers, count):
            ru0, t0 = resource.getrusage(resource.RUSAGE_SELF), time.time()
            cpu0 = svc.judges[key].engine.cpu_seconds()
            per = count // writers
            errs = []

            def w(k):
                for i in range(per):
                    s = streams[(k * per + i) % len(streams)]
                    r = svc.submit(caller, "task.open", {"stream_id": s, "task_id": U("%s-%d-%d" % (label, k, i))})
                    if not isinstance(r, Accepted):
                        errs.append(r)
            ts = [threading.Thread(target=w, args=(k,)) for k in range(writers)]
            [t.start() for t in ts]
            [t.join() for t in ts]
            wall = time.time() - t0
            ru1 = resource.getrusage(resource.RUSAGE_SELF)
            cpu1 = svc.judges[key].engine.cpu_seconds()
            done = per * writers
            assert not errs, errs[:3]
            out[label] = {"commands": done, "streams": len(streams), "writers": writers,
                          "commands_per_s": round(done / wall),
                          "engine_cpu_ms_per_1000": round((cpu1 - cpu0) * 1000 * 1000 / done, 1),
                          "host_cpu_ms_per_1000": round(((ru1.ru_utime + ru1.ru_stime) - (ru0.ru_utime + ru0.ru_stime))
                                                        * 1000 * 1000 / done, 1)}
        s1 = opened()
        run("one_stream_one_writer", [s1], 1, n // 4)
        s2 = opened()
        run("one_stream_32_writers", [s2], 32, n)
        many = [opened() for _ in range(64)]
        run("64_streams_32_writers", many, 32, n)
        total_events = store.count()
        total_bytes = sum(store.stored_bytes(s) for s in store.streams())
        out["stored_bytes_per_event"] = round(total_bytes / total_events, 1)
        chain_bytes = store._exec("SELECT coalesce(sum(octet_length(meta_salt) + octet_length(chain)), 0) FROM events")[0][0]
        out["chain_bytes_per_event"] = round(int(chain_bytes) / total_events, 1)
        out["postgres_bytes_per_event_note"] = "request and event JSON text only, without Postgres row and index overhead"
        svc.close()
        store.close()
        return out
    finally:
        pgtmp.stop(data)
        shutil.rmtree(data, ignore_errors=True)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--n", type=int, default=2000)
    ap.add_argument("--fresh-build", action="store_true")
    ap.add_argument("--out")
    a = ap.parse_args()
    tmp = tempfile.mkdtemp(prefix="provenstream-bench-")
    try:
        commit, core, layer, builds = build(tmp, a.fresh_build)
        edir = os.path.join(tmp, "engines")
        from provenstream.build import install
        install(os.path.join(tmp, "tasks"), edir, say=lambda *x: None)
        result = {
            "machine": {"platform": platform.platform(), "machine": platform.machine(), "cpus": os.cpu_count(),
                        "python": platform.python_version()},
            "when": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "build": builds,
            "engine_tasks": engine_bench(commit, os.path.join(tmp, "tasks", "engine"), a.n),
            "host_tasks": host_bench(commit, edir, a.n),
        }
        print(json.dumps(result, indent=2))
        if a.out:
            os.makedirs(os.path.dirname(os.path.abspath(a.out)), exist_ok=True)
            with open(a.out, "w") as f:
                json.dump(result, f, indent=2)
                f.write("\n")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


if __name__ == "__main__":
    main()
