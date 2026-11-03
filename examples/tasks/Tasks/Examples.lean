-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Tasks.Theorems

/-!
# Worked examples: a stream of tasks

Requests with the answers they get, checked at build time (`#guard`) and compiled into the engine's `--self-test`.
Every rule of the layer and the core's admission refuse something.
-/

namespace Tasks.Examples
open Provenstream Provenstream.Layer Tasks

def url : String := "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/tasks"
def ann : Id := "a0000000-0000-4000-8000-000000000001"   -- the opener
def ben : Id := "b0000000-0000-4000-8000-000000000002"   -- an assignee
def cy : Id := "c0000000-0000-4000-8000-000000000003"    -- anyone else
def S : Id := "50000000-0000-7000-8000-000000000001"
def K1 : Id := "60000000-0000-7000-8000-000000000001"
def K2 : Id := "60000000-0000-7000-8000-000000000002"
def K3 : Id := "60000000-0000-7000-8000-000000000003"

abbrev Sv := tasks.service
def core (c : Id) (cmd : Command) (f : Fresh := []) : Sv.Req := .inl (c, cmd, f)
def task (c : Id) (cmd : TaskCommand) (f : Fresh := []) : Sv.Req := .inr (c, cmd, f)

def story : List (Sv.Req × Option String) :=
  [ (task ann (.open S K1 none none), some "stream_must_exist"),                  -- the core's admission
    (core ann (.streamOpen url none) [S], none),                                  -- position 0
    (task ben (.open S K1 none none), some "only_opener_can_open_tasks"),
    (task ann (.open S K1 none none) [K2], some "fresh_ids_must_match_the_command"),
    (task ann (.open S K1 none (some "the first task")), none),                   -- position 1
    (task ann (.open S K1 none none), some "task_id_must_be_new"),
    (task ann (.open S K2 (some K3) none), some "parent_task_must_exist"),        -- no task K3 yet
    (task ann (.open S K2 (some S) none), some "parent_task_must_exist"),         -- the stream is no task
    (task ann (.open S K2 (some K2) none), some "parent_task_must_exist"),        -- not its own parent
    (task ann (.open S K2 (some K1) (some "a child")), none),                     -- a child of K1, at 2
    (task ben (.assign S K1 ben none), some "only_opener_can_assign"),
    (task ann (.assign S K3 ben none), some "task_must_exist"),
    (task ben (.complete S K1 none), some "only_assignee_can_finish"),            -- an unassigned task
    (task ann (.assign S K1 ben none), none),
    (task ann (.assign S K1 cy none), some "task_is_assigned_once"),
    (task ben (.complete S K3 none), some "task_must_exist"),
    (task ann (.complete S K1 none), some "only_assignee_can_finish"),            -- not even the opener
    (task ben (.complete S K1 (some "done")), none),
    (task ben (.complete S K1 none), some "task_is_completed_once"),
    (task ann (.assign S K2 ann none), none),                                     -- the opener may assign itself
    (core ben (.streamClose S none), some "only_opener_can_close"),
    (core ann (.streamClose S none), none),
    (task ann (.open S K3 none none), some "stream_must_be_open") ]               -- nothing after a close

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
  (tasks.rules.map (·.reason) ++ ["stream_must_exist", "stream_must_be_open"]).all fun r =>
    story.any fun (_, want) => want == some r

#guard everyRuleBites

def allOk : Bool := answersOk && checksOk && everyRuleBites

end Tasks.Examples
