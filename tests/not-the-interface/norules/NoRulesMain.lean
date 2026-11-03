-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import NoRules
import Provenstream.Engine.Step
import NoRulesRevision

/-!
# norules-engine: the interface's commands, without its rules

A valid proof (it builds and proves its theorem) whose engine passes its self-test and describes the core's commands
exactly as the core does, but is not built on `Provenstream.Layer`: it accepts every request, whatever the core's rules
say. Its description matches the stream interface; its answers do not.
-/

namespace NoRules
open Provenstream Provenstream.Wire

def loop (stdin stdout : IO.FS.Stream) : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
    let line ← stdin.getLine
    if line.isEmpty then return
    if line != "\n" then
      stdout.putStrLn (if line.startsWith "{\"query\":\"describe\"" then
        render (Engine.describeJ built coreService) else answer)
      stdout.flush
    loop stdin stdout n

end NoRules

open Provenstream Provenstream.Wire in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--self-test"] => IO.println "norules-engine self-test: ok"; return 0
  | ["--revision"] => IO.println (render (Engine.revisionJ NoRules.built)); return 0
  | ["--describe"] => IO.println (render (Engine.describeJ NoRules.built coreService)); return 0
  | _ =>
    let stdout ← IO.getStdout
    stdout.putStrLn "{\"ready\":true}"
    stdout.flush
    NoRules.loop (← IO.getStdin) stdout 1000000
    return 0
