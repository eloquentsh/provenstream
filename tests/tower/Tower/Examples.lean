-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Tower.Theorems

/-!
# Worked examples: reviews on tasks

Requests with the answers they get, checked at build time (`#guard`) and compiled into the engine's `--self-test`.
Every rule of layer B and its guard refuse something; the core's rules come before the guard.
-/

namespace Tower.Examples
open Provenstream Provenstream.Layer Tasks Tower

def url : String := "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/tests/tower"
def ann : Id := "a0000000-0000-4000-8000-000000000001"   -- the opener
def ben : Id := "b0000000-0000-4000-8000-000000000002"   -- the assignee
def S : Id := "50000000-0000-7000-8000-000000000001"
def K : Id := "60000000-0000-7000-8000-000000000001"
def K2 : Id := "60000000-0000-7000-8000-000000000002"

abbrev Sv := reviews.service
def core (c : Id) (cmd : Command) (f : Fresh := []) : Sv.Req := .inl (.inl (c, cmd, f))
def task (c : Id) (cmd : TaskCommand) : Sv.Req := .inl (.inr (c, cmd, []))
def review (c : Id) (cmd : ReviewCommand) : Sv.Req := .inr (c, cmd, [])

def story : List (Sv.Req × Option String) :=
  [ (review ann (.approve S K none), some "stream_must_exist"),
    (core ann (.streamOpen url none) [S], none),
    (task ann (.open S K none none), none),
    (task ann (.open S K2 (some K) none), none),                                    -- a child of K
    (core ann (.streamClose S none), none),                                         -- nothing completed: closes
    (core ann (.streamOpen url none) [S], some "stream_id_must_be_new") ]

def S2 : Id := "50000000-0000-7000-8000-000000000002"

def story2 : List (Sv.Req × Option String) :=
  [ (core ann (.streamOpen url none) [S2], none),
    (task ann (.open S2 K none none), none),
    (review ann (.approve S2 K none), some "task_must_be_completed"),
    (task ann (.assign S2 K ben none), none),
    (task ben (.complete S2 K none), none),
    (core ben (.streamClose S2 none), some "only_opener_can_close"),                  -- the core's rule first
    (core ann (.streamClose S2 none), some "completed_tasks_must_be_approved_before_close"),  -- B's guard, two down
    (review ben (.approve S2 K none), some "only_opener_can_approve"),
    (review ann (.approve S2 K (some "looks good")), none),
    (review ann (.approve S2 K none), some "task_is_approved_once"),
    (core ann (.streamClose S2 none), none),
    (task ben (.complete S2 K none), some "stream_must_be_open") ]

def answersOk (st : List (Sv.Req × Option String)) : Bool :=
  let (log, answers) := Sv.run (st.map (·.1))
  answers.length == st.length && Sv.check log && (answers.zip st).all fun (x, (_, want)) =>
    match x, want with
    | .accepted _, none => true
    | .rejected r, some r' => r == r'
    | _, _ => false

#guard answersOk story
#guard answersOk story2

def everyRuleBites : Bool :=
  (reviews.rules.map (·.reason) ++ reviews.guards.map (·.reason)).all fun r =>
    story2.any fun (_, want) => want == some r

#guard everyRuleBites

def storyOk : Bool := answersOk story && answersOk story2 && everyRuleBites

end Tower.Examples
