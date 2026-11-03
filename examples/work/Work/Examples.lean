-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Work.Theorems

/-!
# Worked examples: a stream of work

Requests with the answers they get, checked at build time (`#guard`) and compiled into the engine's `--self-test`.
Every rule of the layer and the core's admission refuse something.
-/

namespace Work.Examples
open Provenstream Provenstream.Layer Work

def url : String := "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/work"
def ann : Id := "a0000000-0000-4000-8000-000000000001"   -- the opener
def ben : Id := "b0000000-0000-4000-8000-000000000002"   -- the assignee
def cy : Id := "c0000000-0000-4000-8000-000000000003"    -- a preparer
def dee : Id := "d0000000-0000-4000-8000-000000000004"   -- another preparer
def S : Id := "50000000-0000-7000-8000-000000000001"
def K1 : Id := "60000000-0000-7000-8000-000000000001"
def K2 : Id := "60000000-0000-7000-8000-000000000002"
def K3 : Id := "60000000-0000-7000-8000-000000000003"
def K4 : Id := "60000000-0000-7000-8000-000000000004"

abbrev Sv := work.service
def core (c : Id) (cmd : Command) (f : Fresh := []) : Sv.Req := .inl (c, cmd, f)
def wk (c : Id) (cmd : WorkCommand) (f : Fresh := []) : Sv.Req := .inr (c, cmd, f)

def story : List (Sv.Req × Option String) :=
  [ (wk ann (.create S K1 none), some "stream_must_exist"),                       -- the core's admission
    (core ann (.streamOpen url none) [S], none),                                  -- position 0
    (wk ben (.create S K1 none), some "only_opener_can_create"),
    (wk ann (.create S K1 none) [K2], some "fresh_ids_must_match_the_command"),
    (wk ann (.create S K1 (some "the first item")), none),                        -- position 1
    (wk ann (.create S K1 none), some "work_id_must_be_new"),
    (wk ben (.assign S K1 ben none), some "only_opener_can_assign"),
    (wk ann (.assign S K3 ben none), some "work_must_exist"),
    (wk ben (.ask S K1 cy none), some "only_assignee_can_ask"),                   -- not yet assigned
    (wk ann (.assign S K1 ben none), none),                                       -- position 2
    (wk ann (.assign S K1 cy none), some "work_is_assigned_once"),
    (wk ann (.ask S K1 cy none), some "only_assignee_can_ask"),                   -- not even the opener
    (wk ben (.ask S K3 cy none), some "work_must_exist"),
    (wk ben (.ask S K1 ben none), some "preparer_must_not_be_the_assignee"),
    (wk cy (.reply S K1 none), some "only_asked_preparers_can_reply"),            -- not yet asked
    (wk ben (.ask S K1 cy (some "please prepare")), none),                        -- position 3
    (wk ben (.ask S K1 cy none), some "preparer_is_asked_once"),
    (wk ben (.ask S K1 dee none), none),                                          -- position 4: any number
    (wk ben (.ask S K1 ann none), none),                                          -- position 5: the opener may prepare
    (wk dee (.reply S K3 none), some "work_must_exist"),
    (wk ben (.reply S K1 none), some "only_asked_preparers_can_reply"),           -- the assignee was not asked
    (wk cy (.reply S K1 (some "https://example.org/preparations/cy")), none),     -- position 6
    (wk cy (.reply S K1 none), some "preparer_replies_once"),
    (wk cy (.complete S K1 none), some "only_assignee_can_decide"),
    (wk ann (.cancel S K1 none), some "only_assignee_can_decide"),
    (wk ben (.complete S K3 none), some "work_must_exist"),
    (wk ben (.cancel S K3 none), some "work_must_exist"),
    (wk ben (.complete S K1 (some "done")), none),                                -- position 7: decided
    (wk ben (.complete S K1 none), some "work_is_decided_once"),
    (wk ben (.cancel S K1 none), some "work_is_decided_once"),
    (wk ben (.ask S K1 dee none), some "work_must_be_undecided"),                 -- nothing about K1 follows
    (wk dee (.reply S K1 none), some "work_must_be_undecided"),
    (wk ann (.create S K2 none), none),                                           -- position 8
    (wk ann (.assign S K2 ann none), none),                                       -- position 9: the opener assigns itself
    (wk ann (.cancel S K2 (some "won't be done")), none),                         -- position 10: cancelled, no preparation
    (wk ann (.complete S K2 none), some "work_is_decided_once"),
    (wk ann (.create S K4 none), none),                                           -- position 11
    (wk ben (.complete S K4 none), some "only_assignee_can_decide"),              -- an unassigned item
    (wk ann (.assign S K4 ben none), none),                                       -- position 12
    (wk ben (.complete S K4 none), none),                                         -- position 13: completed without a preparer
    (core ben (.streamClose S none), some "only_opener_can_close"),
    (core ann (.streamClose S none), none),
    (wk ann (.create S K3 none), some "stream_must_be_open") ]                    -- nothing after a close

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
  (work.rules.map (·.reason) ++ ["stream_must_exist", "stream_must_be_open"]).all fun r =>
    story.any fun (_, want) => want == some r

#guard everyRuleBites

def allOk : Bool := answersOk && checksOk && everyRuleBites

end Work.Examples
