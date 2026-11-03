-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Log.Theorems

/-!
# Worked examples: a notebook

Requests with the answers they get, checked at build time (`#guard`) and compiled into the engine's `--self-test`.
Every rule of the layer, and the core's admission, refuses something.
-/

namespace Log.Examples
open Provenstream Provenstream.Layer Log

def url : String := "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/log"
def ann : Id := "a0000000-0000-4000-8000-000000000001"   -- the opener
def ben : Id := "b0000000-0000-4000-8000-000000000002"   -- anyone else
def S : Id := "50000000-0000-7000-8000-000000000001"
def T : Id := "50000000-0000-7000-8000-000000000002"

abbrev Sv := log.service
def core (c : Id) (cmd : Command) (f : Fresh := []) : Sv.Req := .inl (c, cmd, f)
def append (c : Id) (cmd : LogCommand) (f : Fresh := []) : Sv.Req := .inr (c, cmd, f)

def story : List (Sv.Req × Option String) :=
  [ (append ann (.append S "too early" none), some "stream_must_exist"),          -- the core's admission
    (core ann (.streamOpen url none) [S], none),
    (append ann (.append S "first page" (some "a note")), none),
    (append ben (.append S "not mine" none), some "only_opener_can_append"),
    (append ann (.append S "x" none) [T], some "fresh_ids_must_match_the_command"),
    (core ben (.streamOpen url none) [T], none),
    (append ben (.append T "my own notebook" none), none),                         -- openers are per stream
    (append ann (.append T "not mine either" none), some "only_opener_can_append"),
    (append ann (.append S "second page" none), none),
    (core ben (.streamClose S none), some "only_opener_can_close"),
    (core ann (.streamClose S none), none),
    (append ann (.append S "too late" none), some "stream_must_be_open") ]        -- nothing after a close

def answersOk : Bool :=
  let (_, answers) := Sv.run (story.map (·.1))
  answers.length == story.length &&
    (answers.zip story).all fun (x, (_, want)) =>
      match x, want with
      | .accepted _, none => true
      | .rejected r, some r' => r == r'
      | _, _ => false

#guard answersOk

def checksOk : Bool :=
  let (log, answers) := Sv.run (story.map (·.1))
  Sv.check log && (Sv.runS (Sv.init S) ((story.map (·.1)).filter (Sv.reqStream · == S))).2 ==
    (answers.zip (story.map (·.1))).filterMap fun (a, r) => if Sv.reqStream r == S then some a else none

#guard checksOk

def everyRuleBites : Bool :=
  (log.rules.map (·.reason) ++ ["stream_must_exist", "stream_must_be_open"]).all fun r =>
    story.any fun (_, want) => want == some r

#guard everyRuleBites

def allOk : Bool := answersOk && checksOk && everyRuleBites

end Log.Examples
