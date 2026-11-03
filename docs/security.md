# Security and limits

## Who decides what

The engine decides every request from the stream's own events; the host authenticates, fills in each request's
`actor_id` from the token, mints ids, stores, and routes. It attests nothing else: a principal is an id and its tokens,
with no kind. The host's trust is `docs/tcb.md`: a compromised host can lie about callers, refuse service, or serve a
stream with the wrong binary; it cannot make a valid log out of an invalid one without the engine
or a replay (`provenstream verify`) noticing, provided the verifier's engine is built from the stream's revision.

## Limits, enforced

| limit | where |
|---|---|
| request body 1 MiB | host (`protocol.MAX_BODY`, refused by the carrier) |
| one request per message: no batches, no notifications | host (`protocol.py`) |
| 1000 events or rows per page of `stream.events` / `stream.rows` | host (`host.PAGE`) |
| `meta` at most 4096 bytes, no control characters | engine (`validMeta`) |
| revision URL at most 2048 characters, a full commit and a package path | engine and host (`revision_url_must_name_a_commit`), host routing |
| ids are canonical lowercase UUIDs | engine (`validUuid`), host routing |
| JSON depth 32; repeated keys, NaN, lone surrogates refused | engine (`Engine/Json.lean`), host (`wire.py`) |
| batch size 512 requests; 16 compare-and-set retries | host (`service.py`) |
| streams per engine (`--max-streams`), engine idle stop (`--idle-timeout`) | host |
| engine answer timeout 30 s, start 120 s | host (`engine.py`) |
| `idempotency_key` 1 to 200 characters | host |

Not enforced: a per-principal rate or quota (the usage counters measure, they do not limit), the number of streams
or revisions, and memory per engine beyond what `--max-streams` bounds.

## Who may read what

Nobody is kept from reading: any authenticated principal reads any stream (`stream.get`, `stream.events`,
`stream.rows`, `stream.head`, `stream.describe`, `usage.get`), and `revisions.list`, `revision.describe` and `whoami`
answer to any authenticated caller. No proof says who reads (`gap_read_visibility`). Whoever holds the database holds
every stream anyway (`replay`, `export` and `verify` in local mode read it directly). Keep what must stay private out
of `meta`, or erase it: a row whose meta is erased keeps its commitment, so the chain still verifies.

## What an answer gives away

An `unavailable` answer carries `retry: true` and an incident id, never the failure's text (which can hold engine
output, paths or database detail); the host logs the detail under that id. `GET /healthz`, which anyone can ask,
answers `{"ok": true}` or 503 `{"ok": false}`: no counts, no error text.

## Engines are code

An engine is native code built from a proof repository. Install only engines you built, or whose manifest you
checked and rebuilt. The host runs each as a subprocess with the host's privileges and no sandbox; the remote build
path (phase 2) adds sandboxing. `LEAN_ABORT_ON_PANIC=1` is set so a Lean panic kills the engine instead of answering a
default value; the audit checks that no panic is reachable from the decision functions.

## Keys and tokens

Tokens are stored as SHA-256 hashes; one live token per principal; rotation revokes the old one.
