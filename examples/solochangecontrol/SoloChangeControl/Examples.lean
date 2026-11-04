-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import SoloChangeControl.Theorems

/-!
# Worked examples: a stream of changes, one person's

Requests with the answers they get, checked at build time (`#guard`) and compiled into the engine's `--self-test`.
Every rule of the layer and the core's admission refuse something.
-/

namespace SoloChangeControl.Examples
open Provenstream Provenstream.Layer SoloChangeControl

def url : String := "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/solochangecontrol"
def ann : Id := "a0000000-0000-4000-8000-000000000001"   -- the opener, who decides
def ben : Id := "b0000000-0000-4000-8000-000000000002"   -- someone else on the host
def cy : Id := "c0000000-0000-4000-8000-000000000003"    -- a developer
def dee : Id := "d0000000-0000-4000-8000-000000000004"   -- another developer
def eve : Id := "e0000000-0000-4000-8000-000000000005"   -- a reviewer
def fay : Id := "f0000000-0000-4000-8000-000000000006"   -- another reviewer
def S : Id := "50000000-0000-7000-8000-000000000001"
def K1 : Id := "60000000-0000-7000-8000-000000000001"
def K2 : Id := "60000000-0000-7000-8000-000000000002"
def K3 : Id := "60000000-0000-7000-8000-000000000003"
def K4 : Id := "60000000-0000-7000-8000-000000000004"

/-- Revisions, as the harness would name them. -/
def rev (n : String) : String := s!"https://example.org/repo/commit/{n}"
def R0 := rev "r0"
def B1 := rev "b1"
def B2 := rev "b2"
def B3 := rev "b3"
def B4 := rev "b4"
def B5 := rev "b5"
def B6 := rev "b6"
def C1 := rev "c1"
def C2 := rev "c2"
def C3 := rev "c3"
def C4 := rev "c4"
def C5 := rev "c5"
def C6 := rev "c6"
def C7 := rev "c7"
def C8 := rev "c8"
def M := rev "m"
def M2 := rev "m2"
def S1 : String := "https://example.org/screens/s1"
def S2 : String := "https://example.org/screens/s2"
def S3 : String := "https://example.org/screens/s3"

abbrev Sv := solo.service
def core (c : Id) (cmd : Command) (f : Fresh := []) : Sv.Req := .inl (c, cmd, f)
def ck (c : Id) (cmd : ChangeCommand) (f : Fresh := []) : Sv.Req := .inr (c, cmd, f)

def story : List (Sv.Req × Option String) :=
  [ (ck ann (.create S K1 R0 none), some "stream_must_exist"),                   -- the core's admission
    (core ann (.streamOpen url none) [S], none),                                 -- position 0
    (ck ben (.create S K1 R0 none), some "only_opener_can_create"),
    (ck ann (.create S K1 R0 none) [K2], some "fresh_ids_must_match_the_command"),
    (ck ann (.create S K1 R0 (some "the first change")), none),                  -- position 1
    (ck ann (.create S K1 R0 none), some "change_id_must_be_new"),
    (ck ann (.branch S K3 cy B1 none), some "change_must_exist"),
    (ck ben (.branch S K1 cy B1 none), some "only_opener_can_branch"),
    (ck ann (.branch S K1 ann B1 none), some "developer_must_not_be_the_opener"),
    (ck ann (.branch S K1 cy R0 none), some "revisions_must_be_unique"),         -- the change's own revision
    (ck ann (.branch S K1 cy B1 none), none),                                    -- position 2
    (ck ann (.branch S K1 cy B4 none), some "developer_is_branched_once"),
    (ck ann (.branch S K1 dee B1 none), some "revisions_must_be_unique"),        -- another's branch revision
    (ck ann (.branch S K1 dee B2 none), none),                                   -- position 3
    (ck eve (.push S K1 C1 none), some "only_branched_developers_can_push"),
    (ck cy (.push S K1 B1 none), some "revisions_must_be_unique"),               -- its own branch revision
    (ck cy (.push S K1 C1 none), none),                                          -- position 4
    (ck cy (.push S K1 C2 none), none),                                          -- position 5: as often as it likes
    (ck cy (.push S K1 C2 none), some "revisions_must_be_unique"),
    (ck dee (.push S K1 C3 none), none),                                         -- position 6
    (ck ann (.review S K1 C4 S1 none), some "reviewer_must_not_be_the_opener"),
    (ck cy (.review S K1 C4 S1 none), some "reviewer_must_not_be_a_developer"),
    (ck eve (.review S K1 C2 S1 none), some "revisions_must_be_unique"),         -- a developer's revision
    (ck eve (.review S K1 C4 S1 none), none),                                    -- position 7: before the pull
    (ck ann (.branch S K1 eve B3 none), some "developer_must_not_be_a_reviewer"),
    (ck cy (.pull S K1 none), some "only_opener_can_pull"),
    (ck ann (.pull S K3 none), some "change_must_exist"),
    (ck ann (.pull S K1 none), none),                                            -- position 8: incoming work cut off
    (ck ann (.pull S K1 none), some "change_is_pulled_once"),
    (ck ann (.branch S K1 fay B5 none), some "change_must_not_be_pulled"),
    (ck cy (.push S K1 C5 none), some "change_must_not_be_pulled"),
    (ck eve (.review S K1 C6 S2 none), none),                                    -- position 9: the reviewer iterates
    (ck fay (.review S K1 C7 S2 none), none),                                    -- position 10: another reviewer; a screen may repeat
    (ck eve (.merge S K1 M none), some "only_opener_can_decide"),
    (ck ann (.merge S K1 C6 none), some "revisions_must_be_unique"),             -- a reviewer's revision
    (ck ann (.merge S K1 C3 none), some "revisions_must_be_unique"),             -- a developer's revision
    (ck ann (.merge S K1 R0 none), some "revisions_must_be_unique"),             -- merging nothing
    (ck ann (.merge S K3 M none), some "change_must_exist"),
    (ck ann (.merge S K1 M (some "merged to main")), none),                      -- position 11: decided
    (ck ann (.merge S K1 M2 none), some "change_is_decided_once"),
    (ck ann (.abandon S K1 none), some "change_is_decided_once"),
    (ck eve (.review S K1 C8 S3 none), some "change_must_be_undecided"),         -- nothing about K1 follows
    (ck ann (.create S K2 R0 none), none),                                       -- position 12: R0 starts another change
    (ck ann (.abandon S K2 (some "not worth it")), none),                        -- position 13: abandoned, no pull
    (ck ann (.branch S K2 cy B6 none), some "change_must_be_undecided"),
    (ck ann (.create S K4 M none), none),                                        -- position 14: continues K1
    (ck ann (.merge S K4 M2 none), none),                                        -- position 15: alone, no pull, no push
    (ck ann (.abandon S K3 none), some "change_must_exist"),
    (core ben (.streamClose S none), some "only_opener_can_close"),
    (core ann (.streamClose S none), none),
    (ck ann (.create S K3 R0 none), some "stream_must_be_open") ]                 -- nothing after a close

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
  (solo.rules.map (·.reason) ++ ["stream_must_exist", "stream_must_be_open"]).all fun r =>
    story.any fun (_, want) => want == some r

#guard everyRuleBites

def allOk : Bool := answersOk && checksOk && everyRuleBites

end SoloChangeControl.Examples
