# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""Fixtures: a throwaway Postgres cluster (scripts/pgtmp.py), and the six proofs' engines built by the real pipeline
(`provenstream.build`) from one commit of a throwaway git repository holding this checkout's files: the core, the log,
the principals, the tasks, the work and the tower, each a revision of that commit (its package path).

`store` (and so `service` and `people`) runs every test that uses it twice, on a SQLite file and on a Postgres
database (`store_target`); `dsn` is a Postgres database alone, for the tests about Postgres itself."""
import os, shutil, subprocess, sys, tempfile, uuid

import pytest

HERE = os.path.dirname(os.path.abspath(__file__))
HOST = os.path.dirname(HERE)
ROOT = os.path.dirname(HOST)
sys.path.insert(0, HOST)
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import pgtmp  # noqa: E402

# The command line's config directory for every test: an empty one of its own, never ~/.provenstream, so a developer's
# stored tokens and settings neither leak into a test nor get written by one; and no system keychain, ever.
CONFIG_DIR = tempfile.mkdtemp(prefix="provenstream-test-config-")
os.environ["PROVENSTREAM_CONFIG_DIR"] = CONFIG_DIR
os.environ["PYTHON_KEYRING_BACKEND"] = "keyring.backends.null.Keyring"
# And a working directory of its own, outside any checkout and any home: the command line looks for a project file
# (.provenstream/client.json) walking up from the current directory, and must find none a developer left above.
WORK_DIR = tempfile.mkdtemp(prefix="provenstream-test-cwd-")
os.chdir(WORK_DIR)


def U(name: str) -> str:
    """A canonical lowercase UUID named for reading."""
    return str(uuid.uuid5(uuid.NAMESPACE_URL, "provenstream-test:" + name))


def _git(repo, *args):
    subprocess.run(["git", "-C", repo, "-c", "user.name=test", "-c", "user.email=test@example.invalid"] + list(args),
                   check=True, capture_output=True)


PROOFS = {"core": ".", "log": "examples/log", "principals": "examples/principals", "tasks": "examples/tasks",
          "work": "examples/work", "tower": "tests/tower"}


@pytest.fixture(scope="session")
def engines(tmp_path_factory):
    """{"commit": the commit; "core", "log", "principals", "tasks", "work", "tower": each proof's revision key; "urls": {proof:
    revision URL}; "dir": the engines directory; "url": the repository URL; "repo": its path; "builds": {proof: build
    directory}}."""
    from provenstream.build import build_engine, install
    from provenstream.revisions import revision_url, split_key
    base = tmp_path_factory.mktemp("proofs")
    repo = str(base / "repo")
    subprocess.run(["rsync", "-a", "--exclude", ".lake", "--exclude", ".git", "--exclude", "__pycache__",
                    "--exclude", ".pytest_cache", ROOT + "/", repo + "/"], check=True)
    subprocess.run(["git", "init", "-q", repo], check=True)
    _git(repo, "add", "-A")
    _git(repo, "commit", "-qm", "first")
    c1 = subprocess.run(["git", "-C", repo, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    url = "https://example.org/provenstream-test"
    quiet = lambda *a: None
    edir = str(base / "engines")
    out = {"commit": c1, "dir": edir, "url": url, "repo": repo, "builds": {}, "urls": {}}
    for proof, package in PROOFS.items():
        b = str(base / ("b-" + proof))
        build_engine(repo, c1, b, package=package, repo_url=url, reuse_lake=ROOT, say=quiet)
        out[proof] = install(b, edir, say=quiet)
        out["builds"][proof] = b
        out["urls"][proof] = revision_url(url, *split_key(out[proof]))
    return out


@pytest.fixture(scope="session")
def pg_cluster(tmp_path_factory):
    if not pgtmp.available():
        pytest.exit("Postgres is required: install it, or set PROVENSTREAM_PG_BIN to its bin directory", returncode=2)
    data = str(tmp_path_factory.mktemp("pgdata"))
    cluster = pgtmp.start(data)
    yield cluster
    pgtmp.stop(data)


@pytest.fixture
def dsn(pg_cluster):
    return pgtmp.create_db(pg_cluster)


@pytest.fixture(params=["sqlite", "postgres"])
def store_target(request, tmp_path):
    """The target of a store of each kind: a SQLite file, a Postgres database."""
    if request.param == "sqlite":
        return "sqlite:///" + str(tmp_path / "streams.db").lstrip("/")
    return request.getfixturevalue("dsn")


@pytest.fixture
def store(store_target):
    from provenstream.store import open_store
    s = open_store(store_target)
    yield s
    s.close()


def raw_sql(target, sql, args=(), forge=False):
    """Run `sql` on a store's database outside the store, on a connection of its own; with `forge`, first switch off
    the append-only trigger (as someone with the database could), so stored rows can be changed."""
    if target.startswith("sqlite:"):
        import sqlite3
        from provenstream.store_sqlite import sqlite_path
        c = sqlite3.connect(sqlite_path(target), isolation_level=None)
        try:
            if forge:
                c.execute("DROP TRIGGER events_append_only_update")
            c.execute(sql.replace("%s", "?"), tuple(args))
        finally:
            c.close()
    else:
        import psycopg
        with psycopg.connect(target, autocommit=True) as c:
            if forge:
                c.execute("ALTER TABLE events DISABLE TRIGGER events_append_only")
            c.execute(sql, args)


def refused_by_trigger(target):
    """The exception a store's database raises when a trigger refuses a statement."""
    if target.startswith("sqlite:"):
        import sqlite3
        return sqlite3.IntegrityError
    import psycopg
    return psycopg.errors.RaiseException


def revision_map(engines):
    from provenstream.revisions import load_map
    return load_map(os.path.join(engines["dir"], "revisions.json"))


@pytest.fixture
def service(store, engines):
    from provenstream.service import Service
    svc = Service(store, revision_map(engines), snapshot_every=5)
    yield svc
    svc.close()


@pytest.fixture
def people(store):
    """Principals issued by the host: ann, ben, cy, eve and dee. {name: (principal, token)}."""
    out = {}
    for name in ("ann", "ben", "cy", "eve", "dee"):
        p = U(name)
        out[name] = (p, store.create_principal(p))
    return out
