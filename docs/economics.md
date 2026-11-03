# Economics: historical measurements of the previous core

**Every figure on this page is historical.** It was measured on 2026-10-22 against the earlier, four-command core and
its engine protocol 1 (the tasks example then had `task.open` and `task.done`), which the two-command core replaced on
2026-10-30 (commit `62bdcbf`). No run on the current core has been recorded here. `bench/bench.py` now speaks
protocol 2 and runs against today's engines (the core's and the tasks example's, built from a commit and a package
path): run it to reproduce these measurements for the current core, on your hardware. The figures below are kept as
the last measurement, not as today's.

Only measured numbers, from `bench/bench.py` (method in its docstring); raw results in `bench/results/`. Machine: an
Apple arm64 laptop (macOS 15.6, 10 cores), Postgres 16 on a local Unix socket, Python 3.9, two runs on 2026-10-22
(`warm-20261022.json`, `cold-20261022.json`). They are one machine's numbers, not a capacity plan.

## The engine alone (tasks example, one stream, piped)

| measure | warm run | cold run |
|---|---|---|
| process start to `{"ready":true}` | 3.0 ms | 3.0 ms |
| decisions per second (2001 requests: an opening and 2000 `task.open`) | 21,728 | 21,645 |
| CPU for those 2001 decisions (process resource usage) | 0.095 s | 0.096 s |
| peak resident memory | 5.3 MiB | 5.3 MiB |
| stored rows replayed per second, fast path (`sync`) | 30,765 | 29,688 |
| stored rows replayed per second, audit path (`check`, quadratic in the stream's length) | 4,206 | 4,152 |
| binary size | 3,469,456 bytes | same |

The fast path keeps one tag per event of a stream (for references), appended at the end of a list, so its cost per
event grows with the stream's length; these figures are for a 2001-event stream.

## The host (service in process, no HTTP; Postgres on the same machine)

| workload (warm run / cold run) | accepted commands per second | engine CPU per 1000 commands | host process CPU per 1000 commands |
|---|---|---|---|
| one stream, one writer (500 commands) | 2,139 / 2,178 | 20.0 / 40.0 ms | 320 / 316 ms |
| one stream, 32 writers (group commit, 1984 commands) | 5,302 / 5,357 | 50.4 / 50.4 ms | 129 / 128 ms |
| 64 streams, 32 writers (1984 commands) | 2,187 / 2,079 | 20.2 / 20.2 ms | 367 / 380 ms |

Engine CPU here is sampled from the running process with `ps` (10 ms resolution on macOS), so small differences are
noise. Stored bytes per event: 395.1 (request and event JSON text as stored; Postgres row and index overhead not
included).

What the numbers say, and no more: on this machine the engine's decision is a small share of a write's cost; the host
(Python, one transaction per batch) dominates, and batching on one stream amortises it. The audit replay path is for
verification, not serving.

## With the host's hash chain (one run, `warm-20261022-chain.json`)

The same benchmark after the host began computing a salted meta commitment and a hash chain for every row
(`PROTOCOL.md`, "Chain"). One run; the two runs above differ from each other by up to about 5%, so read small changes
as noise.

| workload | accepted commands per second (before → with chain) | host process CPU per 1000 commands (before → with chain) |
|---|---|---|
| one stream, one writer | 2,139 → 2,019 | 320 → 343 ms |
| one stream, 32 writers | 5,302 → 4,994 | 129 → 140 ms |
| 64 streams, 32 writers | 2,187 → 2,154 | 367 → 407 ms |

Stored bytes per event: 395.1 of request and event text, as before, plus 48.0 for the chain (a 16-byte salt and a
32-byte head per row). The engine is unchanged (its figures in this run: 20,314 decisions per second, 5.3 MiB).

## Build

| measure | value |
|---|---|
| base engine, Lake caches reused from a checkout | 1.6 s |
| tasks engine, caches reused | 0.8 s |
| base engine, cold (no caches; the whole core compiled) | 6.0 s |
| tasks engine, cold (core and layer compiled) | 6.1 s |

Toolchain download (about 600 MB once per toolchain) and Docker image builds are not included.
