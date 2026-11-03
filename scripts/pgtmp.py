#!/usr/bin/env python3
# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""A throwaway Postgres cluster in a directory, on a Unix socket, for the tests, check.sh and the audit harness.

    python3 scripts/pgtmp.py start DIR     start a cluster in DIR (created if missing); prints its base DSN
    python3 scripts/pgtmp.py db DIR        create a fresh database in DIR's cluster; prints its DSN
    python3 scripts/pgtmp.py stop DIR      stop DIR's cluster
    python3 scripts/pgtmp.py crash DIR     stop DIR's cluster at once (as a crash would) and start it again

The Postgres binaries are found in PROVENSTREAM_PG_BIN, else on PATH, else in Homebrew's postgresql@16.
"""
from __future__ import annotations
import json, os, shutil, socket, subprocess, sys, tempfile, uuid
from typing import Dict

HOMEBREW = "/opt/homebrew/opt/postgresql@16/bin"


def pg_bin() -> str:
    env = os.environ.get("PROVENSTREAM_PG_BIN")
    if env:
        return env
    found = shutil.which("pg_ctl")
    return os.path.dirname(found) if found else HOMEBREW


def available() -> bool:
    return os.path.exists(os.path.join(pg_bin(), "pg_ctl"))


def start(data: str) -> Dict[str, object]:
    """Start a cluster in `data` (a fresh directory or one this function made); answers {"host", "port"}."""
    os.makedirs(data, exist_ok=True)
    info = os.path.join(data, "provenstream-pg.json")
    env = dict(os.environ, LC_ALL="C", LANG="C")
    if not os.path.exists(os.path.join(data, "PG_VERSION")):
        subprocess.run([os.path.join(pg_bin(), "initdb"), "-D", data, "-U", "provenstream", "--auth=trust", "-E",
                        "UTF8"], check=True, capture_output=True, env=env)
    sockdir = tempfile.mkdtemp(prefix="pspg")          # short: Unix socket paths are limited
    s = socket.socket(); s.bind(("127.0.0.1", 0)); port = s.getsockname()[1]; s.close()
    subprocess.run([os.path.join(pg_bin(), "pg_ctl"), "-D", data, "-l", os.path.join(data, "log"), "-w", "-o",
                    "-k %s -p %d -c listen_addresses=''" % (sockdir, port), "start"], check=True, capture_output=True,
                   env=env)
    cluster = {"host": sockdir, "port": port}
    with open(info, "w") as f:
        json.dump(cluster, f)
    return cluster


def cluster_of(data: str) -> Dict[str, object]:
    with open(os.path.join(data, "provenstream-pg.json")) as f:
        return json.load(f)


def base_dsn(cluster: Dict[str, object]) -> str:
    return "postgresql://provenstream@/postgres?host=%s&port=%d" % (cluster["host"], cluster["port"])


def create_db(cluster: Dict[str, object]) -> str:
    """A fresh, empty database in `cluster`; answers its DSN."""
    import psycopg
    name = "t" + uuid.uuid4().hex[:12]
    with psycopg.connect(base_dsn(cluster), autocommit=True) as c:
        c.execute("CREATE DATABASE %s" % name)
    return "postgresql://provenstream@/%s?host=%s&port=%d" % (name, cluster["host"], cluster["port"])


def crash(data: str) -> None:
    """Stop the cluster immediately (no checkpoint, as a crash) and start it again on the same socket and port."""
    c = cluster_of(data)
    env = dict(os.environ, LC_ALL="C", LANG="C")
    subprocess.run([os.path.join(pg_bin(), "pg_ctl"), "-D", data, "-m", "immediate", "stop"], capture_output=True)
    subprocess.run([os.path.join(pg_bin(), "pg_ctl"), "-D", data, "-l", os.path.join(data, "log"), "-w", "-o",
                    "-k %s -p %d -c listen_addresses=''" % (c["host"], c["port"]), "start"], check=True,
                   capture_output=True, env=env)


def stop(data: str) -> None:
    subprocess.run([os.path.join(pg_bin(), "pg_ctl"), "-D", data, "-m", "immediate", "stop"], capture_output=True)


if __name__ == "__main__":
    cmd, data = sys.argv[1], sys.argv[2]
    if cmd == "start":
        print(base_dsn(start(data)))
    elif cmd == "db":
        print(create_db(cluster_of(data)))
    elif cmd == "stop":
        stop(data)
    elif cmd == "crash":
        crash(data)
    else:
        sys.exit(__doc__)
