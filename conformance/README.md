# Conformance

This is Provenstream's main suite. It is many command sequences, valid and invalid, sent to a host through any
carrier, across the proofs of one commit that have sequences: the core, `examples/log`, `examples/principals`, `examples/tasks`,
`examples/work` and the tower (`tests/tower`); `examples/solochangecontrol`, `examples/email`, `examples/emailtriage` and `examples/email-triage-and-reply` have none yet. Each one comes with its validated outcome: every answer, every refusal and the rule it
names, every event at its seq, and every chain head, read back and recomputed. It also covers the host's own
interface: authentication, parsing, reads, paging, idempotency, `actor_id`, discovery, `principal.create` and the
host's refusals.

A host is **Provenstream-compatible** for protocol 2 when it passes this suite: every case not marked `local_only`, run
by `provenstream conform --base-url` against the host serving the core revision (and, for their themes, that commit's
other proofs). Passing means the host answers callers as [HOST-PROTOCOL.md](../HOST-PROTOCOL.md) says: the same answer
codes, JSON-RPC codes and messages, the same refusal reasons, the same results, in the same order of checks, with ids,
chain heads and receipts that hold together across calls. It says nothing about how the host stores streams or which
language it is written in.

The suite is the host-level sibling of the engine corpus (`corpus/`). There, recorded engine sessions are replayed
byte for byte. Here, sessions of JSON-RPC requests are checked against expected answers, on any carrier.

## Run it

```sh
provenstream conform --engines engines                  # a throwaway host, in process (default --target inprocess)
provenstream conform --engines engines --target stdio   # ... over `serve --stdio`, one session per token
provenstream conform --engines engines --target http    # ... over `serve` on a free localhost port
provenstream conform --engines engines --compare        # all three at once, and the same answer bytes on each
provenstream conform --engines engines --compare --db "$(python3 scripts/pgtmp.py db DIR)"   # the same, on Postgres
```

A local target is a host the runner makes in a temporary directory. It uses a store (a fresh SQLite file, or the
database `--db` names, Postgres included; the run adds streams and principals to it). It serves those proofs'
engines of one commit, from `--engines DIR` (the commit there that serves the core and most of the others, or
`--revision COMMIT`). Without `--engines` it builds them from this checkout's HEAD. It also serves two revisions that
make the host's failures happen: one whose engine is missing (`unavailable`), and one whose engine, a small script the
runner writes, describes itself as no engine of the stream interface (`engine_must_implement_the_interface`). The
runner issues the principals itself, through the operator path: four roles and a spare for each carrier.

`--compare` runs the three carriers in parallel, a thread each, against the one store. Each carrier has its own
principals and its own nonce. Each prints a line per failure (`--verbose`: a line per case), then a summary per
theme (cases, command sequences, passed, failed, skipped) and the time each carrier took.

### Against your own host

```sh
provenstream conform --base-url https://streams.example.org --tokens tokens.json \
  --revision-url https://github.com/you/provenstream/commit/<the core revision the host serves>
```

`tokens.json` is a JSON object that names a token file for each role. The paths are relative to the JSON file:

```json
{"opener": "opener.token", "other": "other.token", "third": "third.token", "outsider": "outsider.token"}
```

The roles are four distinct principals issued by the host (`provenstream host principal create --token-file FILE` on
its database, or `provenstream principal create --token-file FILE` as any of them). They have no kinds and need no
setup: each sequence opens its own streams, and a role is whatever the sequence makes of it (the opener, a principal it
invites or assigns, one it never names). The runner checks each token with `whoami` before the first case and never
prints a token. Of the commit `--revision-url` names, it runs the themes of the proofs the host serves
(`revisions.list`) and skips the rest. A remote run opens streams and creates principals on the host, so use a test
host. It needs no operator access, and it skips the `local_only` cases, which need a broken engine or rotate a token.

The exit code is 0 only if no case failed. It is 2 if the run could not start.

## The cases

`cases/THEME.jsonl` are written by `make_cases.py` (`--check` fails when a file is stale), one case per line. The cases
of a theme run in order, as one session.

| theme | what |
|---|---|
| `core` | sequences on the core: only the opener closes; nothing follows a close; foreign and malformed commands |
| `log` | sequences on `examples/log`: only the opener appends; texts and meta |
| `principals` | sequences on `examples/principals`: admins (the opener, then promoted invitees) invite, promote and summon; agents are never promoted; every declaration once |
| `tasks` | sequences on `examples/tasks`: the opener opens and assigns, the assignee completes; a parent named by its own task_id, a task of the same stream (`parent_task_must_exist`) |
| `work` | sequences on `examples/work`: the opener creates and assigns; the assignee asks preparers other than itself, the asked reply once, the assignee completes or cancels once; nothing about a decided item |
| `tower` | sequences on the tower: reviews by the opener, and no close while a completed task awaits one |
| `auth` | tokens: the roles, no token, an unknown token; a name that is no method is answered before any token is asked for |
| `parse` | messages as bytes: strict JSON, one JSON-RPC 2.0 request object, ids echoed, a message over 1 MiB |
| `reads` | reading is unrestricted: any principal reads any stream; `stream_must_exist`; usage |
| `paging` | `stream.events` and `stream.rows` from `from`, at most `limit`, with `next` |
| `idempotency` | a retry by the same caller gets the first answer; another request is `idempotency_key_must_match_its_request`; another caller's same key is another write |
| `actor` | `actor_id`: filled in from the token, the caller's own accepted, any other refused `actor_id_must_match_the_token` before the stream is asked |
| `discovery` | `rpc.discover`, `revision.describe` (each proof's whole description), `revisions.list` |
| `host` | `principal.create` by any principal (re-issuing a token is the operator's only), `token.rotate` |
| `errors` | names that are no method; URLs that are no revision URL (`revision_url_must_name_a_commit`, read exactly as the core reads it: short or uppercase commits, a `/tree/` without a package or with an empty, `.`, `..` or bad segment, spaces and control characters, over 2048 characters); `revision_must_be_installed`, `repository_must_match_the_engine`, `engine_must_implement_the_interface`, `stream_must_exist`; `unavailable` |

**The proof themes are command sequences.** Each sequence opens a stream of its own and sends it commands by the
roles. Their answers come from a model of the proof's rules in `make_cases.py`, written from the rules' names and
order, not from the Lean, so a host or an engine that differs fails. A command gets the first rule that refuses it:
the core's admission (`stream_must_exist`, `stream_must_be_open`), then the layer's rules in order, and for a core
command a layer's guard after the core's. Otherwise it gets its exact event at its seq. A command the proof
does not describe gets `method_not_found`, params it does not read get `invalid_params`, and an `actor_id` other than
the caller's gets `actor_id_must_match_the_token`. Each sequence ends by reading its stream back, as a role that may or
may not be in it: every event with its seq and the chain head its command's answer gave, the head, the engine's view
(the opener, closed, and what the layer keeps), and the stored rows, whose hash chain the runner recomputes from the
genesis (`"check": "chain"`). Some sequences are written by hand, one or more per rule. The rest come from a seeded
generator, so they are the same on every run and on every machine.

A case is `{"id", "who", "method", "params"?, "expect", "proof"?, "check"?, "local_only"?}`. Instead of a method it can
have `raw` (the message as text), `raw_base64` (as bytes) or `oversize` (a request over 1 MiB the runner builds), and
then `answer_id`, the id its answer carries. `who` is a role, `spare`, `none` (no token; skipped on stdio, where a
session always names its principal), `unknown` (a token no host issued), or `$NAME`, a token an earlier case bound.
`expect` is the answer's `result` or `error`; the runner adds `jsonrpc` and the id. `proof` names the proof (or proofs)
the case needs served, and the case is skipped where the host serves none.

### Patterns

In `expect`, a JSON value is matched exactly: an object's keys as a set, arrays in order, and `1`, `1.0` and `true` are
three values. A string starting with `$` is a pattern:

| pattern | matches |
|---|---|
| `$uuid`, `$hex64`, `$string`, `$int`, `$bool`, `$any` | a value of that shape (`$hex64`: 64 lowercase hex digits, a chain head) |
| `$SHAPE:NAME` | a value of that shape, bound to `NAME` (`"stream_id": "$uuid:s"` binds the stream `stream.open` minted) |
| `$NAME` | exactly what `NAME` is bound to |
| a string holding `${NAME}` | exactly that text with the bound values put in (`"${repo}@${commit}"`) |
| `$$...` | the literal string `$...` |
| `{"$open": true, ...}` | an object holding at least the keys named |
| `{"$contains": [P, ...]}` | an array holding, for each `P`, an element of its own matching it |

These are bound before the first case:

- `$opener`, `$other`, `$third` and `$outsider`: the role principals.
- `$commit` and `$repo`.
- `$rev_P` and `$url_P` for each proof `P` served (`core`, `log`, `principals`, `tasks`, `work`, `tower`): its
  revision and its revision URL.
- `$run`, a nonce of the run.
- Against a host the runner made, also `$spare` (whose token `token.rotate` rotates), `$broken` and `$broken_url` (the
  revision whose engine is missing), and `$notiface` and `$notiface_url` (the one that is no engine of the interface).

In a request, `$NAME` is the bound value and `${NAME}` inside a string is its text. Idempotency keys carry `${run}`, so
a second run against the same host starts afresh.

A `detail` is matched as `$string`. It is prose for people, and its words are not the contract. `data.code`, the
JSON-RPC code and message, and `data.reason` are.

### What `--compare` normalises

Besides each answer matching, `--compare` requires the in-process, stdio and HTTP answers to each case to be the same
bytes, each in the host's canonical form (compact JSON, keys in the host's order, UTF-8 unescaped). Before comparing,
it replaces with the pattern's own text exactly the positions the case's pattern writes as a binding (`$SHAPE:NAME`), a
reference (`$NAME`), or `$uuid`, `$hex64` or `$any`. Those are the values that differ from run to run by design:

- minted stream ids and the role principals;
- chain heads (each row's hash covers a fresh salt);
- incident ids and rotated tokens;
- stored rows' request and event texts and meta salts in `stream.rows`;
- usage counters, and the `running` flag of `revisions.list`.

Everything else is compared as sent, including details and the `$string`, `$int` and `$bool` positions.

## Not covered

- Core rules no host lets a caller reach: `stream_id_must_be_new` and `fresh_ids_must_match_the_command`, because the
  host mints every fresh id. (`revision_url_must_name_a_commit` is reached: the host applies it itself, reading the URL
  exactly as the core does, before it routes the open; a missing or non-string URL is `invalid_params`.)
- What only the operator can do in process (re-issuing a token with `principal_id`, `principal_must_have_no_token`).
  Also carrier framing a JSON-RPC message cannot express (empty lines, `\r\n`, an HTTP body cut off). These are in
  `host/tests/`.
