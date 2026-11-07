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
#guard validPageUrl "none" && validPageUrl C && !validPageUrl "nothing"
#guard validOutcome "done" && validOutcome "not_run" && !validOutcome "sent"
#guard validMode "readonly" && validMode "action_allowed" && !validMode "admin"

/-! What may run. -/

def ro : List Note := [("action", K1, bro), ("mode", K1, readonly)]
def aa : List Note := [("action", K1, bro), ("mode", K1, actionAllowed)]
#guard !mayRun ro K1 && !mayRun aa K1                                       -- no answer, no run, in either mode
#guard mayRun (ro ++ [("approved", K1, jev)]) K1 && mayRun (aa ++ [("approved", K1, jev)]) K1
#guard !mayRun (ro ++ [("rejected", K1, jev)]) K1                           -- a rejection stops it
#guard mayRun (aa ++ [("rejected", K1, jev)]) K1                            -- action_allowed overrides it
#guard runnable (aa ++ [("rejected", K1, jev)]) == [K1]
#guard runnable (ro ++ [("rejected", K1, jev)]) == []

abbrev Sv := actions.service
def core (c : Id) (cmd : Command) (f : Fresh := []) : Sv.Req := .inl (c, cmd, f)
def ck (c : Id) (cmd : ActionCommand) (f : Fresh := []) : Sv.Req := .inr (c, cmd, f)
def ask (k : Id) (f : String := "readonly") : ActionCommand := .evaluate S k C C f none

def story : List (Sv.Req × Option String) :=
  [ (ck bro (ask K1), some "stream_must_exist"),                                          -- the core's admission
    (core ann (.streamOpen url none) [S], none),
    (ck ben (.nameEvaluator S jev none), some "only_opener_can_name_evaluators"),
    (ck ann (.nameEvaluator S ann none), some "evaluator_must_not_be_the_opener"),
    (ck ann (.nameEvaluator S jev none), none),
    (ck ann (.nameEvaluator S jev none), some "evaluator_is_named_once"),
    (ck jev (.approve S K1 none), some "action_must_exist"),
    (ck bro (.evaluate S K1 "https://example.org/c.json" C "readonly" none), some "context_url_must_be_pinned"),
    (ck bro (.evaluate S K1 C "https://example.org/page.md" "readonly" none), some "page_url_must_be_pinned"),
    (ck bro (.evaluate S K9 C "none" "readonly" none), none),                             -- an action on no page
    (ck bro (ask K1), none),
    (ck bro (ask K1), some "action_id_must_be_new"),
    (ck ben (.approve S K1 none), some "only_opener_or_evaluator_can_answer"),
    (ck bro (.approve S K1 none), some "only_opener_or_evaluator_can_answer"),
    (ck jev (.approve S K1 (some "score 120")), none),                                    -- an evaluator approves
    (ck ann (.reject S K1 none), some "action_is_answered_once"),
    (ck bro (ask K2 "action_allowed"), none),
    (ck jev (.reject S K2 (some "completes the task")), none),                            -- recorded, then overridden
    (ck jev (ask K3), none),                                                              -- an evaluator asks
    (ck jev (.approve S K3 none), some "asker_must_not_answer"),
    (ck ann (.reject S K3 (some "no")), none),
    (ck jev (.approve S K3 none), some "asker_must_not_answer"),
    (ck bro (ask K4), none),
    (ck jev (.reject S K4 none), none),                                                   -- an evaluator rejects
    (ck ann (.approve S K4 none), some "action_is_answered_once"),                        -- a rejection stands
    (ck bro (.record S K9 "done" C none), some "an_attempt_must_be_allowed"),             -- never answered
    (ck jev (.record S K1 "done" C none), some "only_the_asker_records"),
    (ck bro (.record S K1 "done" "https://example.org/result.json" none), some "result_url_must_be_pinned"),
    (ck bro (.record S K1 "done" C none), none),                                         -- approved, so it may have run
    (ck bro (.record S K1 "failed" C none), some "action_is_recorded_once"),
    (ck bro (.record S K4 "done" C none), some "an_attempt_must_be_allowed"),             -- rejected in readonly
    (ck bro (.record S K4 "not_run" C none), none),
    (ck bro (.record S K2 "done" C none), none),                                         -- rejected, overridden in action_allowed
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
