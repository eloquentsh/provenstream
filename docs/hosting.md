# Hosting

One generic host (`host/provenstream`, Python) serves every revision it has an engine for. It has no per-layer code
and no principal logic driven by any proof: it reads each engine's description and builds its request handling from
it.

## Revisions, engines and the engines directory

A **revision** is a commit and a package path, so one commit serves all its proofs side by side. Its URL names both:
`<repo>/commit/<commit>` (or `<repo>#<commit>`, `<repo>@<commit>`) for the repository's root package,
`<repo>/tree/<commit>/<package>` for another (`<commit>`: 40 or 64 lowercase hex digits; `<package>`: `/`-separated
segments of `[A-Za-z0-9._-]`, none empty, `.` or `..`). Its key, everywhere the host names it, is `<commit>` for the
root package and `<commit>/<package>` for another. One commit of this repository is a revision per proof:

| proof | revision key | URL |
|---|---|---|
| the core | `<commit>` | `<repo>/commit/<commit>` |
| `examples/log` | `<commit>/examples/log` | `<repo>/tree/<commit>/examples/log` |
| `examples/principals` | `<commit>/examples/principals` | `<repo>/tree/<commit>/examples/principals` |
| `examples/tasks` | `<commit>/examples/tasks` | `<repo>/tree/<commit>/examples/tasks` |
| `examples/work` | `<commit>/examples/work` | `<repo>/tree/<commit>/examples/work` |
| `examples/solochangecontrol` | `<commit>/examples/solochangecontrol` | `<repo>/tree/<commit>/examples/solochangecontrol` |
| the tower | `<commit>/tests/tower` | `<repo>/tree/<commit>/tests/tower` |

- **Build**: `provenstream engine build --repo R --commit C --out B [--package P]` takes the commit's files only
  (`git archive`), stamps the package's revision module with the commit, the repository URL and the package, runs
  `lake build` with the toolchain the package's `lean-toolchain` pins, checks that the proof inherits from the core's
  (`project.inherits`), runs the engine's self-test, description and the interface check, and writes `B/engine` and
  `B/PROVENANCE.json` (revision key, repository and proof URL, commit and tree, package, toolchain and `lean
  --version`, builder platform, engine sha256 and size, advertised schema, build time). It prints `{revision,
  proof_url, engine}`. `--reuse-lake DIR` copies Lake's build directories from a checkout first, to save time.
  `docker/build-engine.sh REPO COMMIT [PACKAGE]` does the same in a container (linux engines).
- **Install**: `provenstream engine install B --engines DIR` checks the sha256 against the manifest, runs the
  self-test, checks that the engine describes itself as the manifest says (its commit, package and schema) and that it
  implements the stream interface, copies it to `DIR/<commit>/<package or _root>/` (the engine, its
  `PROVENANCE.json`, and the `THIRD_PARTY_NOTICES` and `LICENSE` that travel with it), and adds it to
  `DIR/revisions.json` under its revision key. It never replaces an installed revision. One commit's six engines:

  ```
  engines/revisions.json
  engines/<commit>/_root/engine                  (and PROVENANCE.json, THIRD_PARTY_NOTICES and LICENSE beside each)
  engines/<commit>/examples/log/engine
  engines/<commit>/examples/principals/engine
  engines/<commit>/examples/tasks/engine
  engines/<commit>/examples/work/engine
  engines/<commit>/tests/tower/engine
  ```

- **Rebuild check**: building the same commit again on the same platform gave the same bytes in our tests
  (`test_build_install_never_replaces`); across platforms the bytes differ, and `provenstream verify` checks behaviour
  instead: it replays a stream's stored rows through an engine you build yourself from the stream's commit and package.

## The host

`provenstream serve --engines DIR` keeps its streams in the SQLite file `~/.provenstream/streams.db` (Python's standard
library: no database server). `--db` (or `PROVENSTREAM_DATABASE_URL`) names another store: `sqlite:///abs/path.db` or a
path ending `.db`, or Postgres as `postgresql://...` or `host=... dbname=...` (`pip install 'provenstream[postgres]'`;
`postgresql://` alone uses libpq's own settings). Several hosts may share one Postgres database; a SQLite file is for
one host, beside which local commands may still write. `provenstream export FILE` writes every stream's rows with their
salts and chain heads (no tokens), and `provenstream import FILE` stores them in a store without those streams after
recomputing every chain, so streams move from SQLite to Postgres, or back. Or `docker compose -f
docker/docker-compose.yml up` (Postgres 16 and the host on `127.0.0.1:${PROVENSTREAM_PORT:-8080}`, engines mounted
read-only from `docker/engines`, which `docker/build-engine.sh` fills).

- **Routing**: a `stream.open` names its revision by URL; every later command is routed by the stream's row 0. A
  stream whose revision has no engine here is not served, by any engine.
- **One process per revision, on demand**: an engine starts on the first request that needs it; the host reads its
  description and checks that it reports exactly the revision it is listed under (its commit and its package) and
  protocol 2; it stops after `--idle-timeout` seconds without use (no process for an idle revision). Streams reload
  lazily: from a snapshot this process re-folded, else from their rows.
- **Eviction**: each engine holds at most `--max-streams` streams; the least recently used are dropped.
- **Writes**: per stream, one in-process owner batches requests, decides them against the engine, and appends the
  batch with one compare-and-set in the store (one `BEGIN IMMEDIATE` transaction in SQLite); a lost append is decided
  again.
- **Request handling from the description**: the host takes the command's params as the description lists them,
  fills in `actor_id` from the token (and refuses one naming another principal, `actor_id_must_match_the_token`,
  before the stream is asked), mints the fresh ids, and checks every answer against the description (the stream and
  position it decided at, the actor, the minted ids, the event's name); a mismatch kills the engine and stores
  nothing. It attests nothing else: there are no kinds.
- **Opening**: a `stream.open` whose URL is no revision URL is refused with the core's own rule,
  `revision_url_must_name_a_commit`, read exactly as the core reads it (it names no engine to ask). Then
  `revision_must_be_installed` (no engine here for that commit and package), `repository_must_match_the_engine` (the
  URL names another repository than the engine was built from; compared after normalising `http`/`https`, a trailing
  `/` or `.git`, the host's case, and the path's case on github.com), and `engine_must_implement_the_interface` (the
  engine does not answer the core's recorded sessions as the core does: `host/provenstream/interface.py`).
- **Idempotency**: an `idempotency_key` returns the stored answer to a retry, and
  `idempotency_key_must_match_its_request` to a different request under the same key. A key is the caller's own: the
  same key from two callers is two writes.
- **Engine environment**: an engine starts with `PATH` and `LEAN_ABORT_ON_PANIC=1` only; none of the host's settings
  (its database URL, `PG*`, tokens) reach it.
- **Principals and tokens**: a principal is an id and its tokens, nothing more: no kind, no role, no account. The
  first principal of a new host comes from its operator: `provenstream host principal create --token-file FILE`
  (local mode, on the database; the token is written to FILE, created 0600, and only `{principal_id}` is printed;
  without `--token-file` it prints `{principal_id, token}`). After that any signed-in principal may ask the host for
  another (`principal.create`; `provenstream principal create --token-file FILE` or `--save-as NAME`, which prints only
  the new id). After `import`, which moves no tokens, the operator issues an existing principal a token again with
  `host principal create --id <principal> --token-file FILE` (`principal.create {principal_id}`, the operator only:
  `only_the_operator_can_reissue_a_principal` for a token's caller, `principal_must_have_no_token` for an id that
  holds one). Tokens are stored as SHA-256 hashes; `token.rotate` replaces the caller's.
- **Usage**: per stream and per revision, `received`, `accepted`, `events`, `bytes` (appended by this host),
  `bytes_stored` (exact, from the table), `engine_ms` (an estimate: wall time of engine calls), `cpu_ms` (measured
  from the engine process: exact for reaped processes, sampled while running; per revision), `last_active`
  (`usage.get`).
- **Replay**: `provenstream replay` replays every stream through its revision's engine on the audit path;
  `provenstream verify` replays one stream (from the database, a host, or a rows file) through an engine given, taken
  from an engines directory, or built from the stream's commit (`--repo`; `--package` defaults to the package the
  stream's revision names).

## Reads

Reading is the host's business, and it restricts nothing: any authenticated principal reads any stream
(`stream.get`, `stream.events`, `stream.rows`, `stream.head`, `stream.describe`, `usage.get`). No proof says who
reads (gap_read_visibility). A read of a stream with no rows is refused `stream_must_exist`. Whoever runs a host holds
its database, and so every stream, anyway; keep what must stay private out of `meta`, or erase it.

## The chain

Each stream's stored rows form a hash chain computed by the host (`host/provenstream/chain.py`; exact definition in
`PROTOCOL.md`, "Chain"). For each accepted row the host draws a 16-byte salt, commits to `meta` as `sha256:` of salt
and meta, hashes the row with `meta` replaced by that commitment, and stores the salt and the new head in the same
compare-and-set append. A write's answer carries the head (`chain`): a receipt. `stream.head` and `stream.events`
show heads; `stream.rows` gives salts and heads, so anyone can recompute. `provenstream verify` and `replay` recompute
every commitment and the chain, refuse at the first mismatch naming the seq, and with `--head` check heads a client
kept. Rows written before the chain are hashed with an empty salt (never stored: rows are append-only) and the chain
continues from there. A row whose meta is erased keeps its commitment, so the chain still verifies, but its content
cannot be checked and an engine cannot replay it; verify reports "meta erased".

Any change to a stream's history before a head someone holds is detectable. The chain does not detect truncation after
the last head a client kept, nor an operator who recomputes the whole chain; signed receipts and published heads
(planned) address those.

## HTTP and stdio

Every method, param, result and error is in [HOST-PROTOCOL.md](../HOST-PROTOCOL.md), generated from the code, and a
host answers `rpc.discover` with the same as an OpenRPC document. JSON-RPC 2.0 on `POST /rpc`, `GET /healthz`; or
`provenstream serve --stdio`, one request per line on stdin and one answer per line on stdout, as one principal for
the session (`--as` or `--token-file`), the same bytes as the HTTP body. The HTTP carrier (`host/provenstream/api.py`)
only moves bytes; the methods and paging are `host/provenstream/host.py` (`Host.handle`, the one function every
carrier and the command line's local mode call), and the messages and the answer table are
`host/provenstream/protocol.py`. Protocol 2 takes one request per message: batches and notifications are
`invalid_request`. A command is its name with its params, for example (the token read from a file, never in a
process's arguments):

```sh
curl -s localhost:8080/rpc -H @<(printf 'Authorization: Bearer %s' "$(cat me.token)") \
  -d '{"jsonrpc":"2.0","id":1,"method":"task.open","params":{"stream_id":"<id>","task_id":"<id>"}}'
```

Every error's `data.code` names its kind: `parse_error`, `invalid_request`, `method_not_found` (also a command the
stream's revision does not describe, its `data.detail` naming the revision), `invalid_params` (`data.detail`),
`unauthorized`, `refused` (`data.reason`: the rule broken), `unavailable` (`data.retry: true` and `data.incident`: the
failure is in the host's log under that id, never in the answer). `stream.events` and `stream.rows` page: `from`
(default 0), `limit` (default and most 1000), and `next` in the answer, the `from` of the next page or null at the
end. `GET /healthz` is `{"ok": true}`, or 503 `{"ok": false}` when the store does not answer: no counts, no error
text.

## The command line: remote and local modes

Each invocation runs in one mode (`host/provenstream/mode.py`): `PROVENSTREAM_MODE` if set; else local if `--db` or
`PROVENSTREAM_DATABASE_URL`; else local for a local-only command when no base URL is named either, with the default
database `~/.provenstream/streams.db`; else remote. `DATABASE_URL`, the `PG*` variables and the configured
`default_host` never choose it.

- **Remote**: `open`, `close`, `call` (`api`), `principal create`, `events`, `head`, `revisions`, `verify` go to the
  host at `--base-url` (else `PROVENSTREAM_BASE_URL`, else the project file's host, else the configured
  `default_host`, else the local host, `provenstream serve` on its default port) as the principal of `--token-file`,
  else `PROVENSTREAM_TOKEN`, else the
  token `provenstream login` stored for that host (`host/provenstream/auth.py`: the system keychain with the keyring
  extra, else `~/.provenstream/credentials.json`, 0600). `--principal P` (a principal id or a name given with
  `principal create --save-as`) sends another stored principal's token. A token is never printed, and a stored one is
  only sent to the host it was stored for. `auth` (`login`, `logout`, `whoami`) is remote only: exit 8 in local mode.
- **Local**: the same commands run in process against the database, with the engines of `--engines` (else
  `PROVENSTREAM_ENGINES`, else the configured `local.engines`), through the same `Host.handle` as `serve`. Writes act
  as `--as PRINCIPAL` (a principal the store knows) and go through the same compare-and-set append, so they
  interleave safely with a running host. Reads need no `--as`: they are unrestricted. `revisions` reads the engines
  directory. `serve`, `host principal create`, `token rotate`, `replay`, `export` and `import` are local only (exit 7
  in remote mode). Local mode is operator access: `--as` needs no token, as anyone with the database could act
  anyway; the proofs still decide every write.
- **Files**: `init`, `check`, `build`, `describe`, `install`, `config`, `help`, `stream use`, `stream alias` touch
  no host and no database.

The commands form a tree (`stream open|close|head|events|verify|use|alias`, `revision`, `api`, `principal create`,
`status`, `auth`, `host ...`, `engine ...`, `conform`, `config`); the flat verbs are aliases of it, building the same
arguments (`host/provenstream/cli.py`, `cli_stream.py`; `provenstream help` lists them). The command line fills in
`actor_id` from the signed-in principal (`--as` in local mode; the stored login's principal; for a bare token, from
`whoami`) unless the caller gave one.

Before sending a proof command (`stream open`, `stream close`, `api`), the command line checks the method and params
against the revision's description: a local engine's `--describe` when `--proof` names one, else the host's
`revision.describe` (in local mode, the engines directory's engine), cached under
`~/.provenstream/proofs/<commit>/<package or _root>/description.json`. It answers `method_not_found` or
`invalid_params` itself (exit 5) and sends nothing; the rules stay the host's. With no description to be had it fails
with a clear message (exit 6). It never compiles Lean for a stream or proof command. `provenstream -h --proof PROOF`
prints the description as Markdown.

The current stream, which `head`, `events` and `verify` fall back to, is a flag, else `PROVENSTREAM_STREAM`, else the
nearest `.provenstream/client.json` above the current directory (a project file: `host`, `proof_revision_url`,
`stream`, `aliases`, no secrets), else the user config (`host/provenstream/context.py`). A project's `host` ranks with
`default_host`, below `--base-url` and `PROVENSTREAM_BASE_URL`, and never chooses the mode. `close` (either form)
never uses the current stream, and asks for a confirmation on a terminal showing the stream's opener; without one it
needs `--yes` or `--confirm STREAM` (exit 2), and `--dry-run` sends nothing. JSON-RPC callers, the conformance runner
among them, are unaffected: the confirmation is the command line's.

Mixing the modes' settings is an error (exit 8): a base URL in local mode, `--as` in remote mode, `--principal` in
local mode, `--db` with `PROVENSTREAM_MODE=remote`. Exit codes: 3 unauthorized, 4 refused (`refused: <rule>`), 5
method not found or invalid params, 6 unavailable (or no description to be had), 7 needs local mode, 8 mode
misconfigured. `provenstream status [--json]` prints the resolved mode, what decided it and the target (password
redacted), and in remote mode the token's principal (`whoami`).

## Conformance against your host

`provenstream conform --base-url URL --tokens tokens.json --revision-url <the core revision's URL>` runs the
conformance suite against a host you run: four distinct principals' token files (`opener`, `other`, `third`,
`outsider`; issue them with `host principal create --token-file` or `principal create --token-file`), and the
commit's other proofs' themes where the host serves them. It opens streams and creates principals, so use a test host.
See [conformance/README.md](../conformance/README.md).

## Left out

A WebSocket listener, any read authorisation (gap_read_visibility), backups, and remote builds (`docs/phase2.md`).
