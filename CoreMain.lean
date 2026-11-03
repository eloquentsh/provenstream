-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Engine.Step
import Provenstream.Examples
import CoreRevision

/-!
# core-engine

The engine of the core alone: streams with `stream.open` and `stream.close`, and nothing else. A long-lived process speaking JSON lines on stdin and stdout (`PROTOCOL.md`).

    core-engine                  serve (it starts empty and prints {"ready":true})
    core-engine --self-test      run the worked examples through the compiled code
    core-engine --revision       print {"revision", "repo", "package"}
    core-engine --describe       print {"revision", "repo", "package", "protocol", "schema"}
-/

open Provenstream Provenstream.Wire

def fail (msg : String) : IO UInt32 := do
  IO.eprintln s!"core-engine: {msg}"
  return 2

/-- The worked examples, through the compiled code (the `#guard`s run them in the interpreter at build time). -/
def selfTest : IO UInt32 := do
  let bad := Examples.cases.filter fun (log, e, want) =>
    rejection log e != want || rejectionS (fold e.stream log) e != want
  let badChecks := Examples.validLogs.filter (!check ·)
  let badRun := !Examples.commandsProduceEvents
  let badJson := !(sampleRequests.all roundTripRequest && eventsRoundTrip && badLines.all refuses && badNumbersRefused
    && objectsKeepOrder && keyOrder && surrogates && duplicateKeys && nesting && escapes && numbers && refusals)
  if bad.isEmpty && badChecks.isEmpty && !badRun && !badJson then
    IO.println s!"core-engine self-test: {Examples.cases.length} cases (rules and fast path), {Examples.validLogs.length} valid logs, run, json: ok"
    return 0
  else
    fail s!"self-test failed: {bad.length} cases, {badChecks.length} valid logs, run {badRun}, json {badJson}"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--self-test"] => selfTest
  | ["--revision"] => IO.println (render (Engine.revisionJ coreBuilt)); return 0
  | ["--describe"] => IO.println (render (Engine.describeJ coreBuilt coreService)); return 0
  | [] => Engine.serveStdioAt coreService coreBuilt (← IO.getStdout); return 0
  | _ => fail "usage: core-engine | core-engine --self-test | core-engine --revision | core-engine --describe"
