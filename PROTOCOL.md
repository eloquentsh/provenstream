# The engine's line protocol

Every engine (the core's `core-engine`, a layer's, a tower's) speaks the same protocol, protocol 2: one JSON value per
line on stdin, one per line on stdout, in order, one answer per non-empty line. It prints `{"ready":true}` first. It
holds no storage: everything it knows of a stream it was told on this connection.

This is the inner protocol, host to engine, between parts that trust each other. Callers never speak it: they speak
JSON-RPC to the host, described in [HOST-PROTOCOL.md](HOST-PROTOCOL.md) (generated from the host's code).

```
ENGINE                 serve
ENGINE --self-test     run the worked examples through the compiled code; exit 0 when they pass
ENGINE --revision      {"revision": <commit>, "repo": <url>, "package": <package path, "" for the root>}
ENGINE --describe      {"schema", "revision", "repo", "protocol", "package"}
```

Answers have no whitespace; objects' keys are printed in descending order. Ids are canonical lowercase UUIDs.
`meta`, wherever it appears, is absent, `null`, or a string of at most 4096 UTF-8 bytes with no control character.

## Requests

```json
{"actor_id": "<id>", "command": {"command": "<name>", ...params}, "fresh": ["<id>", ...]}
```

`actor_id` is the caller: the host fills it in from the token (and refuses a caller's `actor_id` that is not the
token's principal before it asks the engine), so the engine always has it. `fresh` holds the ids the host minted for
the command, as many as its description's `fresh` says. A request is answered

```json
{"stream_id": "<id>", "event": {...}, "at": 3, "accept": true}
{"stream_id": "<id>", "reason": "<rule>", "at": 3, "accept": false}
{"error": "malformed", "detail": "..."}
```

`stream_id` is the stream the request is on (for `stream.open`, the minted id), and `at` the stream's length the request
was decided at: an accepted event goes at position `at`. A host that stores events appends it only if the stream still
has `at` events (compare and set); otherwise it drops the stream (`drop`), syncs again and resends. A wrong number of
fresh ids is refused `fresh_ids_must_match_the_command` before any rule (for an open with more than one, on the
stream `""`). A request that does not decode (an unknown command, a missing or unknown key, an old field name, an id
that is not a canonical UUID, a bad `meta`) is `malformed`, with a detail for people.

An accepted event is the command's params with the command's name replaced by its event's (past tense, under
`event`), plus `actor_id` and the minted ids. A real session with the tasks layer's engine:

```
{"ready":true}
> {"actor_id":"a0000000-0000-4000-8000-000000000001","command":{"command":"stream.open","proof_revision_url":"https://example.org/provenstream/tree/4f1c2a9e7b03d6185a2c4e90f7d1b38c6a5e2f04/examples/tasks"},"fresh":["50000000-0000-7000-8000-000000000001"]}
{"stream_id":"50000000-0000-7000-8000-000000000001","event":{"stream_id":"50000000-0000-7000-8000-000000000001","proof_revision_url":"https://example.org/provenstream/tree/4f1c2a9e7b03d6185a2c4e90f7d1b38c6a5e2f04/examples/tasks","meta":null,"event":"stream.opened","actor_id":"a0000000-0000-4000-8000-000000000001"},"at":0,"accept":true}
> {"actor_id":"a0000000-0000-4000-8000-000000000001","command":{"command":"task.open","stream_id":"50000000-0000-7000-8000-000000000001","task_id":"70000000-0000-4000-8000-000000000002","parent_task_id":"70000000-0000-4000-8000-000000000001"},"fresh":[]}
{"stream_id":"50000000-0000-7000-8000-000000000001","reason":"parent_task_must_exist","at":1,"accept":false}
> {"actor_id":"a0000000-0000-4000-8000-000000000001","command":{"command":"task.open","stream_id":"50000000-0000-7000-8000-000000000001","task_id":"70000000-0000-4000-8000-000000000001"},"fresh":[]}
{"stream_id":"50000000-0000-7000-8000-000000000001","event":{"task_id":"70000000-0000-4000-8000-000000000001","stream_id":"50000000-0000-7000-8000-000000000001","parent_task_id":null,"meta":null,"event":"task.opened","actor_id":"a0000000-0000-4000-8000-000000000001"},"at":1,"accept":true}
> {"actor_id":"a0000000-0000-4000-8000-000000000001","command":{"command":"task.open","stream_id":"50000000-0000-7000-8000-000000000001","task_id":"70000000-0000-4000-8000-000000000002","parent_task_id":"70000000-0000-4000-8000-000000000001"},"fresh":[]}
{"stream_id":"50000000-0000-7000-8000-000000000001","event":{"task_id":"70000000-0000-4000-8000-000000000002","stream_id":"50000000-0000-7000-8000-000000000001","parent_task_id":"70000000-0000-4000-8000-000000000001","meta":null,"event":"task.opened","actor_id":"a0000000-0000-4000-8000-000000000001"},"at":2,"accept":true}
> {"actor_id":"b0000000-0000-4000-8000-000000000002","command":{"command":"task.complete","stream_id":"50000000-0000-7000-8000-000000000001","task_id":"70000000-0000-4000-8000-000000000001"},"fresh":[]}
{"stream_id":"50000000-0000-7000-8000-000000000001","reason":"only_assignee_can_finish","at":3,"accept":false}
```

(`>` marks a line sent; it is not part of the protocol.)

## The description

`{"query": "describe"}` (or `ENGINE --describe`) answers `{"schema", "revision", "repo", "protocol", "package"}`:
the schema the engine decodes with, the commit it was built from, the repository URL, `"protocol": 2`, and the package
path of the proof inside the repository (`""` for the root package). `{"query": "schema"}` answers the schema alone,
`{"commands": [...]}`, and `{"query": "revision"}` the revision alone. A host serves engines of protocol 2 only. Each
command, as the core's engine describes `stream.close`:

```json
{"who": "the stream's opener", "stream_id": "stream_id",
 "rules": ["stream_must_exist", "stream_must_be_open", "only_opener_can_close"],
 "params": [{"name": "stream_id", "kind": "uuid"}, {"name": "meta", "kind": "meta"}],
 "name": "stream.close", "minted": [], "fresh": 0,
 "event": {"name": "stream.closed", "fields": ["event", "stream_id", "actor_id", "meta"]}}
```

- `name`: the command; `params`: its keys besides `command`, in order, each with its field kind: `uuid`, `uuid?`
  (a canonical UUID, or absent or `null`), `meta`, `ref` (a natural number, or absent or `null`: the 0-based position
  of an earlier event of the same stream), or a named text (`text`, or a layer's own name) whose form the engine
  checks. The tasks layer's `parent_task_id` is a `uuid?`: the parent's own `task_id`.
- `fresh`, `minted`: how many fresh ids the command takes, and the event fields they become.
- `stream_id`: the name of the param (or minted field) that carries the stream's id (`"stream_id"` for every
  command of the core and the examples, hence `"stream_id": "stream_id"`).
- `who`: when the proof says it, a sentence saying who may send the command.
- `event`: the event an accepted command becomes, its name and its fields in order.
- `rules`: the names of the rules that can refuse it, in the order they are tried: the core's admission
  (`stream_must_exist`, `stream_must_be_open`) for every command but `stream.open`, the mechanism's
  `ref_must_name_an_earlier_event` for a command with a `ref` param, then the proof's own rules (for a core command
  in a layer, the core's rules, then the layer's guards). `fresh_ids_must_match_the_command` is not listed: only a
  broken host meets it.

The schema printed is the list the engine decodes with: whatever decodes names an entry and has only its keys, and
every well-formed request is on the wire as its entry, with exactly its keys (`requestFromJ_schema`,
`requestToJ_schema`, proved for the core and for every layer).

## The core's commands (every engine)

| command | params | fresh | event | who |
|---|---|---|---|---|
| `stream.open` | `proof_revision_url` (text), `meta` | 1: `stream_id` | `stream.opened {event, stream_id, actor_id, meta, proof_revision_url}` | anyone signed in; the caller becomes the stream's opener |
| `stream.close` | `stream_id`, `meta` | 0 | `stream.closed {event, stream_id, actor_id, meta}` | the stream's opener |

`proof_revision_url` names a commit and a package: `<scheme>://<host>/<path>` then `/commit/`, `#` or `@` and a full
40 or 64 digit lowercase hex commit (the repository's root package), or `/tree/`, the commit, `/` and a package path
(one or more `/`-separated segments of `[A-Za-z0-9._-]`, none empty, `.` or `..`); no whitespace or control
character, at most 2048 characters (`validRevisionUrl`). Rules, in order (the first that fails is the `reason`):
`stream_id_must_be_new` and `revision_url_must_name_a_commit` for `stream.open`; `stream_must_exist`,
`stream_must_be_open` and `only_opener_can_close` for `stream.close` (`docs/model.md`).

Every layer event is first asked the core's admission (`stream_must_exist`, `stream_must_be_open`; any actor is
admitted); then the mechanism's check of its references (a `ref` param naming a position not yet in the stream is
refused `ref_must_name_an_earlier_event`; no example layer has a `ref` param); then the layer's rules and reference
rules, in order. On a core command, the
core's rules come first and a layer's guards after.

## Reads and the host's cache

| message | answer |
|---|---|
| `{"query": "stream", "stream_id": s}` | the stream as the rules see it: the core's `stream_id`, `opener_id`, `proof_revision_url`, `closed`, and what a layer keeps (the tasks layer adds `tasks`, `assigned`, `completed`); or `{"error": "stream_must_exist"}` for a stream the engine holds no event of |
| `{"sync": {"stream_id": s, "from": k, "rows": [{"request", "event"}, ...]}}` | fold stored rows onto `s`, which must hold exactly `k` events: `{"synced": s, "length": n}`, `{"length": n, "error": "out_of_sync"}`, or `{"error": "refused", "detail"}` when a row is refused or its event is not its request's |
| `{"load": {"stream_id": s, "k": k, "state": state}}` | set `s` from a snapshot, taken as given (the host re-folds before trusting one): `{"loaded": s, "length": k}` |
| `{"snapshot": s}` | `{"stream_id": s, "state": state, "k": n}` |
| `{"check": {"stream_id": s, "rows": [...]}}` | replay rows from empty through the specification (the audit path, quadratic): `{"state", "length": n, "checked": s}` or `{"error": "refused", "detail"}` |
| `{"drop": s}` | forget `s`: `{"dropped": s}` |

A stored row is `{"request", "event"}`: the request as sent (with its `actor_id` and `fresh`) and the event the
engine answered. A state is the engine's own JSON for a stream (the core's: `url`, `stream`, `opener`, `opened`,
`closed`; a layer's adds `tags` and `layer`, under `core`); the host stores it as a snapshot and passes it back
unread. An empty sync of a stream the engine does not hold, and a refusal on one, create no entry.

A real session with the core's engine (the `state` is the engine's own, stored and passed back unread):

```
{"ready":true}
> {"sync":{"stream_id":"50000000-0000-7000-8000-000000000001","from":0,"rows":[{"request":{"actor_id":"a0000000-0000-4000-8000-000000000001","command":{"command":"stream.open","proof_revision_url":"https://example.org/provenstream/commit/4f1c2a9e7b03d6185a2c4e90f7d1b38c6a5e2f04"},"fresh":["50000000-0000-7000-8000-000000000001"]},"event":{"stream_id":"50000000-0000-7000-8000-000000000001","proof_revision_url":"https://example.org/provenstream/commit/4f1c2a9e7b03d6185a2c4e90f7d1b38c6a5e2f04","meta":null,"event":"stream.opened","actor_id":"a0000000-0000-4000-8000-000000000001"}}]}}
{"synced":"50000000-0000-7000-8000-000000000001","length":1}
> {"query":"stream","stream_id":"50000000-0000-7000-8000-000000000001"}
{"stream_id":"50000000-0000-7000-8000-000000000001","proof_revision_url":"https://example.org/provenstream/commit/4f1c2a9e7b03d6185a2c4e90f7d1b38c6a5e2f04","opener_id":"a0000000-0000-4000-8000-000000000001","closed":false}
> {"snapshot":"50000000-0000-7000-8000-000000000001"}
{"stream_id":"50000000-0000-7000-8000-000000000001","state":{"url":"https://example.org/provenstream/commit/4f1c2a9e7b03d6185a2c4e90f7d1b38c6a5e2f04","stream":"50000000-0000-7000-8000-000000000001","opener":"a0000000-0000-4000-8000-000000000001","opened":true,"closed":false},"k":1}
> {"check":{"stream_id":"50000000-0000-7000-8000-000000000001","rows":[{"request":{"actor_id":"a0000000-0000-4000-8000-000000000001","command":{"command":"stream.open","proof_revision_url":"https://example.org/provenstream/commit/4f1c2a9e7b03d6185a2c4e90f7d1b38c6a5e2f04"},"fresh":["50000000-0000-7000-8000-000000000001"]},"event":{"stream_id":"50000000-0000-7000-8000-000000000001","proof_revision_url":"https://example.org/provenstream/commit/4f1c2a9e7b03d6185a2c4e90f7d1b38c6a5e2f04","meta":null,"event":"stream.opened","actor_id":"a0000000-0000-4000-8000-000000000001"}}]}}
{"state":{"url":"https://example.org/provenstream/commit/4f1c2a9e7b03d6185a2c4e90f7d1b38c6a5e2f04","stream":"50000000-0000-7000-8000-000000000001","opener":"a0000000-0000-4000-8000-000000000001","opened":true,"closed":false},"length":1,"checked":"50000000-0000-7000-8000-000000000001"}
> {"drop":"50000000-0000-7000-8000-000000000001"}
{"dropped":"50000000-0000-7000-8000-000000000001"}
> {"sync":{"stream_id":"50000000-0000-7000-8000-000000000001","from":1,"rows":[]}}
{"length":0,"error":"out_of_sync"}
```

The corpus (`corpus/sessions`: the core's, the log's, the principals', the tasks' and the tower's) records sessions
of these engines byte for byte, the descriptions included; `corpus/replay` checks them.

## Chain (the host's, not the engine's)

The host keeps a hash chain per stream over its stored rows, with `meta` committed by a salted hash
(`host/provenstream/chain.py`, whose docstring is the specification). The engine and the proofs do not see it.

- **Fields**: each stored row has `meta_salt` (16 random bytes, fresh per row, also for rows without meta) and
  `chain` (the stream's head after the row). `stream.rows` returns both, hex; `stream.events` returns each event's
  `chain`; `stream.head {stream_id}` returns `{"stream_id", "length", "chain"}`. (These are the host's methods, to
  callers: `host/provenstream/host.py`, where the two lists page from a cursor and answer any authenticated
  principal.)
- **Receipt**: an accepted write answers `{"seq", "event", "chain"}`, `chain` the head after that row; an idempotent
  retry answers the same.
- **Commitment**: `"sha256:" + hex(SHA-256(salt || UTF-8(meta)))`.
- **Redaction**: R is the stored request with `command.meta` replaced by the commitment, E the stored event with `meta`
  replaced by it, each re-serialised compactly in stored key order; without meta, the stored request and event.
- **Hash**: `h_genesis = SHA-256("provenstream-chain-v1" || 0x00 || UTF-8(stream))`;
  `h_n = SHA-256(h_{n-1} || u64be(n) || u32be(len R) || R || u32be(len E) || E)`.
- **Legacy rows** (written before the chain: no salt, no head) are hashed with an empty salt, never stored; the chain
  continues from the computed head.
- **Erased meta**: a row may carry `meta_commitment` with `null` in place of its meta; the chain still verifies, its
  content can no longer be checked, and an engine cannot replay it.

Any change to a stream's history before a head someone holds is detectable. The chain does not detect truncation after
the last head a client kept, nor an operator who recomputes the whole chain; signed receipts and published heads
(planned) address those.
