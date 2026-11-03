-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Std.Data.HashMap
import Provenstream.Engine.Json
import Provenstream.Layer

/-!
# The engine: its per-stream entries and its messages, for any service

One engine serves every `Service` (`Service.lean`): the base (`coreService`) and the base with a layer or a tower of
layers (`Layer.service L`, `Layered.main`). It keeps, per stream, an `Entry` (a state and the number of events it
folds), loaded lazily: the host syncs a stream's stored rows before it asks for a decision on that stream, and the
engine applies `entrySync` (proved: `entrySync_spec`). A request is decided with `entryRequest` (proved:
`entryRequest_spec`: the answer is `respond`, the new entry is `run`'s, the position is the stream's length). What this
file adds unproved is the map from stream ids to entries, the parsing of messages and the printing of answers.

Messages, one JSON value per line (`PROTOCOL.md`):
- a request `{"actor_id", "command": {...}, "fresh": [...]}`: answers as `responseToJ`, plus `"stream_id"` and `"at"`;
  or `{"error": "malformed", "detail"}`;
- `{"sync": {"stream_id", "from", "rows"}}`, `{"load": {"stream_id", "k", "state"}}`, `{"snapshot": s}`,
  `{"check": {"stream_id", "rows"}}`, `{"drop": s}`: the host's cache of stored streams;
- `{"query": "stream", "stream_id": s}`: a read of stream `s` (the service's `streamSJ`);
- `{"query": "schema"}`: the commands the engine decodes, as `schemaJ S.schema S.rulesOf` (the schema it decodes with,
  each command with its event and the names of the rules that judge it);
- `{"query": "describe"}`: the same schema with the revision the engine was built from (commit, repository, package)
  and its protocol (answered by the serving loop, `stepLineAt`), so a host builds its request handling from it;
- `{"query": "revision"}`: the revision alone.

A layer's engine is `def main := Provenstream.Engine.Layered.mainAt myLayer "name" selfTest built`, where `built` is
the revision `scripts/stamp_revision` writes before the build.
-/

namespace Provenstream.Engine
open Provenstream Provenstream.Wire

/-- The revision an engine was built from: the commit (`git rev-parse HEAD`, with `-dirty` appended when the tree had
uncommitted changes, or `unknown` when the build was not stamped), the repository URL it was built from, and the
package path of the proof inside the repository (`""` for the repository's root package). Not proved to be the source
it was compiled from (gap_engine_is_revision). -/
structure Revision where
  commit : String
  repo : String
  package : String

/-- An engine whose build was not stamped. -/
def Revision.unknown : Revision := ⟨"unknown", "", ""⟩

def revisionJ (r : Revision) : J :=
  .obj [("revision", .str r.commit), ("repo", .str r.repo), ("package", .str r.package)]

/-- The engine protocol (`PROTOCOL.md`) an engine says it speaks in its description. -/
def engineProtocol : Nat := 2

/-- What an engine built from `r` says of itself: its revision (commit, repository, package), the engine protocol it
speaks, and the schema it decodes with, each command with its event and the names of the rules that judge it. -/
def describeJ (r : Revision) (S : Service) : J :=
  .obj [("revision", .str r.commit), ("repo", .str r.repo), ("package", .str r.package),
        ("protocol", .num engineProtocol), ("schema", schemaJ S.schema S.rulesOf)]

variable (S : Service)

abbrev Cache := Std.HashMap Id S.Entry

def withAt (j : J) (s : Id) (n : Nat) : J :=
  match j with
  | .obj kvs => .obj (kvs ++ [("stream_id", .str s), ("at", .num n)])
  | j => j

def num? : Option J → Option Nat
  | some (.num n) => some n
  | _ => none

def obj? : Option J → Option Fields
  | some (.obj kvs) => some kvs
  | _ => none

def str? : Option J → Option String
  | some (.str s) => some s
  | _ => none

/-- The entry for stream `s`: the cached one, or the empty stream's (`Entry.empty_eq`). -/
def cur (c : Cache S) (s : Id) : S.Entry := c.getD s (Service.Entry.empty S s)

def onSync (c : Cache S) (sk : Fields) : Cache S × J :=
  match get? sk "stream_id", num? (get? sk "from"), get? sk "rows" with
  | some (.str s), some k, some (.arr rs) =>
    let en := cur S c s
    match rs.mapM S.rowFromJ with
    | .error d => (c, malformedJ d)
    | .ok rows =>
      match S.entrySync en k rows with                                     -- proved: entrySync_spec
      | .ok en' =>
        -- an empty sync of a stream the engine does not hold creates no entry (reads of unknown streams stay free)
        let c' := if rows.isEmpty && !c.contains s then c else c.insert s en'
        (c', .obj [("synced", .str s), ("length", .num en'.len)])
      | .error "out_of_sync" => (c, .obj [("error", .str "out_of_sync"), ("length", .num en.len)])
      | .error d => (c, .obj [("error", .str "refused"), ("detail", .str d)])
  | _, _, _ => (c, malformedJ "sync: expected {stream_id, from, rows}")

/-- A snapshot's state is set as given; the host verifies it before loading. -/
def onLoad (c : Cache S) (lk : Fields) : Cache S × J :=
  match get? lk "stream_id", num? (get? lk "k"), get? lk "state" with
  | some (.str s), some k, some sj =>
    match S.stateFromJ sj with
    | .ok st => if S.stStream st = s then (c.insert s ⟨st, k⟩, .obj [("loaded", .str s), ("length", .num k)])
                else (c, malformedJ "load: the state is of another stream")
    | .error d => (c, malformedJ d)
  | _, _, _ => (c, malformedJ "load: expected {stream_id, k, state}")

def onCheck (ck : Fields) : J :=
  match get? ck "stream_id", get? ck "rows" with
  | some (.str s), some (.arr rs) =>
    match rs.mapM S.rowFromJ with
    | .error d => malformedJ d
    | .ok rows =>
      if !(rows.all fun (r, _) => S.reqStream r == s) then
        .obj [("error", .str "refused"), ("detail", .str "a stored row is on another stream")]
      else
        match S.replayRows rows with
        | .ok log =>
          if S.check log then
            .obj [("checked", .str s), ("length", .num log.length), ("state", S.stateToJ (S.fold s log))]
          else .obj [("error", .str "refused"), ("detail", .str "check refused the log")]
        | .error d => .obj [("error", .str "refused"), ("detail", .str d)]
  | _, _ => malformedJ "check: expected {stream_id, rows}"

def onRequest (c : Cache S) (j : J) : Cache S × J :=
  match S.requestFromJ j with
  | .error d => (c, malformedJ d)
  | .ok r =>
    let s := S.reqStream r
    let (en', resp, pos) := S.entryRequest (cur S c s) r                   -- proved: entryRequest_spec
    -- a refusal on a stream the engine does not hold creates no entry
    let c' := match resp with
      | .rejected _ => if c.contains s then c.insert s en' else c
      | .accepted _ => c.insert s en'
    (c', withAt (S.responseToJ resp) s pos)

/-- One parsed message against the cache. (Each key is read through `obj?`/`str?`, an `Option`, so that the chain of
fall-throughs stays linear in the generated code: matching `some (.obj _)` directly made the compiler copy every later
branch once per non-matching constructor, and this one function came to 800,000 lines of C.) -/
def step (c : Cache S) (j : J) : Cache S × J :=
  let kvs := match j with | .obj kvs => kvs | _ => []
  if let some sk := obj? (get? kvs "sync") then onSync S c sk
  else if let some lk := obj? (get? kvs "load") then onLoad S c lk
  else if let some s := str? (get? kvs "snapshot") then
    let en := cur S c s
    (c, .obj [("stream_id", .str s), ("k", .num en.len), ("state", S.stateToJ en.st)])
  else if let some ck := obj? (get? kvs "check") then (c, onCheck S ck)
  else if let some s := str? (get? kvs "drop") then (c.erase s, .obj [("dropped", .str s)])
  else if str? (get? kvs "query") == some "schema" then (c, schemaJ S.schema S.rulesOf)
  else if str? (get? kvs "query") == some "stream" then
    match str? (get? kvs "stream_id") with
    | some s => (c, S.streamSJ (cur S c s).st)
    | none => (c, malformedJ "query: expected a stream_id")
  else onRequest S c j

/-- One line: parse (unproved), `step`, render (unproved). -/
def stepLine (c : Cache S) (line : String) : Cache S × String :=
  match parseLine line with
  | .error d => (c, render (malformedJ d))
  | .ok j => let (c', out) := step S c j; (c', render out)

/-- One line, for an engine built from `rev`: `{"query": "revision"}` is answered with `rev`, every other line as
`stepLine` answers it (so no answer of `step` changes). -/
def stepLineAt (rev : Revision) (c : Cache S) (line : String) : Cache S × String :=
  match parseLine line with
  | .error d => (c, render (malformedJ d))
  | .ok j =>
    let kvs := match j with | .obj kvs => kvs | _ => []
    if str? (get? kvs "query") == some "revision" then (c, render (revisionJ rev))
    else if str? (get? kvs "query") == some "describe" then (c, render (describeJ rev S))
    else let (c', out) := step S c j; (c', render out)

/-- The serving loop: one line in, one line out, the per-stream cache carried in a mutable variable. An iterative
loop, so its stack does not grow with the number of lines (the audit found an earlier recursive loop overflowing
after about 130,000 lines). -/
def serveAt (rev : Revision) (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  let mut cache : Cache S := {}
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := line.trimAsciiEnd.copy
    if line.isEmpty then continue
    let (cache', out) := stepLineAt S rev cache line
    cache := cache'
    stdout.putStrLn out
    stdout.flush

/-- The serving loop of an engine that does not know its revision (it reports `unknown`). -/
def serve (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := serveAt S .unknown stdin stdout

/-- Print `{"ready":true}`, then serve stdin as an engine built from `rev`. -/
def serveStdioAt (rev : Revision) (stdout : IO.FS.Stream) : IO Unit := do
  stdout.putStrLn (render (.obj [("ready", .bool true)]))
  stdout.flush
  serveAt S rev (← IO.getStdin) stdout

/-- Print `{"ready":true}`, then serve stdin (revision `unknown`). -/
def serveStdio (stdout : IO.FS.Stream) : IO Unit := serveStdioAt S .unknown stdout

namespace Layered

/-- A layer's engine built from `rev`: serve the combined service, `--self-test` with the layer's own worked
examples, `--revision` (print `{"revision", "repo", "package"}`) or `--describe` (print `{"revision", "repo",
"package", "protocol", "schema"}`). -/
def mainAt {B : Base} (L : Layer B) (name : String) (selfTest : IO Bool) (rev : Revision) (args : List String) :
    IO UInt32 := do
  match args with
  | ["--self-test"] =>
    if ← selfTest then IO.println s!"{name} self-test: ok"; return 0
    else IO.eprintln s!"{name}: self-test failed"; return 2
  | ["--revision"] => IO.println (render (revisionJ rev)); return 0
  | ["--describe"] => IO.println (render (describeJ rev L.service)); return 0
  | [] => serveStdioAt L.service rev (← IO.getStdout); return 0
  | _ => IO.eprintln s!"usage: {name} | {name} --self-test | {name} --revision | {name} --describe"; return 2

/-- A layer's engine that does not know its revision (it reports `unknown`): `mainAt` at `Revision.unknown`. -/
def main {B : Base} (L : Layer B) (name : String) (selfTest : IO Bool) (args : List String) : IO UInt32 :=
  mainAt L name selfTest .unknown args

end Layered

end Provenstream.Engine
