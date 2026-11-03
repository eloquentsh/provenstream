#!/bin/sh
# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
# The host's tests: the six proofs' engines (core, log, principals, tasks, work, tower) built by the real pipeline from one
# commit of a throwaway copy of this checkout, a throwaway Postgres cluster (scripts/pgtmp.py), then pytest
# (host/tests/): the environment (build, install, the command line, -h and -h --proof, config, the keyring, the
# interface check, the store and the service on SQLite and Postgres) and the conformance suite (conformance/, through
# test_conform.py: every sequence on the three carriers at once, on SQLite and on Postgres).
#
# Needs the Lean side built (scripts/check.sh), Postgres binaries (PATH, PROVENSTREAM_PG_BIN or Homebrew's
# postgresql@16 at /opt/homebrew/opt/postgresql@16/bin), and python3 with starlette, uvicorn, psycopg, pytest and httpx
# (pip install './host[postgres,test]').
#
#   scripts/test_host.sh [PYTEST ARGS...]
set -eu
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
if [ -z "${PROVENSTREAM_PG_BIN:-}" ] && ! command -v pg_ctl >/dev/null 2>&1 && \
   [ -x /opt/homebrew/opt/postgresql@16/bin/pg_ctl ]; then
  PROVENSTREAM_PG_BIN=/opt/homebrew/opt/postgresql@16/bin; export PROVENSTREAM_PG_BIN
fi
PATH="${PATH}:${HOME}/.elan/bin"; export PATH
cd "$ROOT/host"
exec "${PYTHON:-python3}" -m pytest -q tests "$@"
