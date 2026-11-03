-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Counter
import Provenstream.Engine.Step
import CounterRevision

/-!
# counter-engine: an interface of its own

A valid proof of a command and event stream (`counter.add`, a fold and a theorem about it) with a self-test and a
description, but not the stream interface: none of the core's commands (no `stream.open`, no `stream.close`).
-/

namespace Counter

def describe (commit repo package : String) : String :=
  "{\"schema\":{\"commands\":[{\"name\":\"counter.add\",\"params\":[{\"name\":\"stream_id\",\"kind\":\"uuid\"}," ++
  "{\"name\":\"n\",\"kind\":\"text\"}],\"fresh\":0,\"minted\":[],\"stream_id\":\"stream_id\"," ++
  "\"event\":{\"name\":\"counter.added\",\"fields\":[\"event\",\"stream_id\",\"actor_id\",\"n\"]},\"rules\":[]}]}," ++
  "\"revision\":\"" ++ commit ++ "\",\"repo\":\"" ++ repo ++ "\",\"package\":\"" ++ package ++ "\",\"protocol\":2}"

def loop (stdin stdout : IO.FS.Stream) : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
    let line ← stdin.getLine
    if line.isEmpty then return
    if line != "\n" then
      stdout.putStrLn (if line.startsWith "{\"query\":\"describe\"" then describe built.commit built.repo built.package
        else "{\"error\":\"malformed\",\"detail\":\"not a counter command\"}")
      stdout.flush
    loop stdin stdout n

end Counter

open Provenstream Provenstream.Wire in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--self-test"] =>
    if Counter.total [.add 1, .add 2] == 3 then IO.println "counter-engine self-test: ok"; return 0 else return 1
  | ["--revision"] => IO.println (render (Engine.revisionJ Counter.built)); return 0
  | ["--describe"] => IO.println (Counter.describe Counter.built.commit Counter.built.repo Counter.built.package); return 0
  | _ =>
    let stdout ← IO.getStdout
    stdout.putStrLn "{\"ready\":true}"
    stdout.flush
    Counter.loop (← IO.getStdin) stdout 1000000
    return 0
