-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Action.Theorems

/-!
# Worked examples: a gate in front of one person's browser

Requests with the answers they get, checked at build time (`#guard`) and compiled into the engine's `--self-test`.
Every rule of the layer and the core's admission refuse something.
-/

namespace Action.Examples
open Provenstream Provenstream.Layer Action

def url : String := "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/action"
def ann : Id := "a0000000-0000-4000-8000-000000000001"   -- the opener
def ben : Id := "b0000000-0000-4000-8000-000000000002"   -- someone else on the host
def bro : Id := "c0000000-0000-4000-8000-000000000003"   -- the broker, who asks
def jev : Id := "d0000000-0000-4000-8000-000000000004"   -- an evaluator
def S : Id := "50000000-0000-7000-8000-000000000001"
def K1 : Id := "60000000-0000-7000-8000-000000000001"
def K2 : Id := "60000000-0000-7000-8000-000000000002"
def K3 : Id := "60000000-0000-7000-8000-000000000003"
def K4 : Id := "60000000-0000-7000-8000-000000000004"
def K9 : Id := "60000000-0000-7000-8000-000000000009"

def C : String :=
  let h := String.ofList (List.replicate 64 'a')
  s!"https://blobs.example.org/b/{h}#sha256={h}&name=context.json"

#guard validUrl C && pinned C
#guard validUrl "http://127.0.0.1:8791/c.json" && !pinned "http://127.0.0.1:8791/c.json"
#guard !pinned "https://example.org/x#sha256=abc"
#guard !validUrl "not a url"
#guard validForced "true" && validForced "false" && !validForced "maybe"

abbrev Sv := actions.service
def core (c : Id) (cmd : Command) (f : Fresh := []) : Sv.Req := .inl (c, cmd, f)
def ck (c : Id) (cmd : ActionCommand) (f : Fresh := []) : Sv.Req := .inr (c, cmd, f)
def ask (k : Id) (f : String := "false") : ActionCommand := .evaluate S k C f none

def story : List (Sv.Req × Option String) :=
  [ (ck bro (ask K1), some "stream_must_exist"),                                          -- the core's admission
    (core ann (.streamOpen url none) [S], none),
    (ck ben (.nameEvaluator S jev none), some "only_opener_can_name_evaluators"),
    (ck ann (.nameEvaluator S ann none), some "evaluator_must_not_be_the_opener"),
    (ck ann (.nameEvaluator S jev none), none),
    (ck ann (.nameEvaluator S jev none), some "evaluator_is_named_once"),
    (ck jev (.approve S K1 none), some "action_must_exist"),
    (ck bro (.evaluate S K1 "https://example.org/c.json" "false" none), some "context_url_must_be_pinned"),
    (ck bro (ask K1), none),
    (ck bro (ask K1), some "action_id_must_be_new"),
    (ck ben (.approve S K1 none), some "only_opener_or_evaluator_can_answer"),
    (ck bro (.approve S K1 none), some "only_opener_or_evaluator_can_answer"),
    (ck jev (.approve S K1 (some "score 120")), none),                                    -- an evaluator approves
    (ck ann (.reject S K1 none), some "action_is_answered_once"),
    (ck bro (ask K2 "true"), none),                                                       -- forced
    (ck jev (.approve S K2 none), some "forced_needs_the_opener"),
    (ck ann (.approve S K2 (some "yes")), none),                                          -- the opener may
    (ck jev (ask K3), none),                                                              -- an evaluator asks
    (ck jev (.approve S K3 none), some "asker_must_not_answer"),
    (ck ann (.reject S K3 (some "no")), none),
    (ck jev (.approve S K3 none), some "asker_must_not_answer"),
    (ck bro (ask K4), none),
    (ck jev (.reject S K4 none), none),                                                   -- an evaluator rejects
    (ck ann (.approve S K4 none), some "action_is_answered_once"),                        -- a rejection stands
    (core ben (.streamClose S none), some "only_opener_can_close"),
    (core ann (.streamClose S none), none),
    (ck bro (ask K9), some "stream_must_be_open") ]                                       -- nothing after a close

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
  Sv.check log && (Sv.runS (Sv.init S) (story.map (·.1))).2 == answers

#guard checksOk

def everyRuleBites : Bool :=
  (actions.rules.map (·.reason) ++ ["stream_must_exist", "stream_must_be_open"]).all fun r =>
    story.any fun (_, want) => want == some r

#guard everyRuleBites

def allOk : Bool := answersOk && checksOk && everyRuleBites

end Action.Examples
