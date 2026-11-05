-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import EmailTriage.Theorems

/-!
# Worked examples: a stream of inbound email triages, one person's

Requests with the answers they get, checked at build time (`#guard`) and compiled into the engine's `--self-test`.
Every rule of the layer and the core's admission refuse something.
-/

namespace EmailTriage.Examples
open Provenstream Provenstream.Layer EmailTriage

def url : String := "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/emailtriage"
def ann : Id := "a0000000-0000-4000-8000-000000000001"   -- the opener, who decides
def ben : Id := "b0000000-0000-4000-8000-000000000002"   -- someone else on the host
def cy : Id := "c0000000-0000-4000-8000-000000000003"    -- an adviser
def dee : Id := "d0000000-0000-4000-8000-000000000004"   -- another adviser
def eve : Id := "e0000000-0000-4000-8000-000000000005"   -- a reviewer
def fay : Id := "f0000000-0000-4000-8000-000000000006"   -- another reviewer
def S : Id := "50000000-0000-7000-8000-000000000001"
def K1 : Id := "60000000-0000-7000-8000-000000000001"
def K2 : Id := "60000000-0000-7000-8000-000000000002"
def K3 : Id := "60000000-0000-7000-8000-000000000003"
def E1 : Id := "70000000-0000-7000-8000-000000000001"   -- an email on the email proof's stream
def E2 : Id := "70000000-0000-7000-8000-000000000002"

/-- The inbound messages, as the harness would name them. -/
def eml (n : String) : String := s!"eloquentmail://personal/{n}.eml"
def M1 := eml "m1"
def M2 := eml "m2"
def M3 := eml "m3"

abbrev Sv := inbound.service
def core (c : Id) (cmd : Command) (f : Fresh := []) : Sv.Req := .inl (c, cmd, f)
def ck (c : Id) (cmd : TriageCommand) (f : Fresh := []) : Sv.Req := .inr (c, cmd, f)

def story : List (Sv.Req × Option String) :=
  [ (ck ann (.create S K1 M1 none), some "stream_must_exist"),                        -- the core's admission
    (core ann (.streamOpen url none) [S], none),                                       -- position 0
    (ck ben (.create S K1 M1 none), some "only_opener_can_create"),
    (ck ann (.create S K1 M1 none) [K2], some "fresh_ids_must_match_the_command"),
    (ck ann (.create S K1 M1 (some "a catch-up cancelled")), none),                    -- position 1
    (ck ann (.create S K1 M1 none), some "triage_id_must_be_new"),
    (ck ann (.ask S K3 cy none), some "triage_must_exist"),
    (ck ben (.ask S K1 cy none), some "only_opener_can_ask"),
    (ck ann (.ask S K1 ann none), some "adviser_must_not_be_the_opener"),
    (ck ann (.ask S K1 cy none), none),                                                -- position 2
    (ck ann (.ask S K1 cy none), some "adviser_is_asked_once"),
    (ck ann (.ask S K1 dee none), none),                                               -- position 3
    (ck eve (.advise S K1 "reply" none), some "only_asked_advisers_can_advise"),
    (ck cy (.advise S K1 "reply" (some "a person wrote and waits")), none),            -- position 4
    (ck cy (.advise S K1 "ignore" none), some "adviser_advises_once"),
    (ck dee (.advise S K1 "ignore" (some "calendar machinery")), none),               -- position 5
    (ck ann (.review S K1 "reply" none), some "reviewer_must_not_be_the_opener"),
    (ck cy (.review S K1 "reply" none), some "reviewer_must_not_be_an_adviser"),
    (ck eve (.review S K3 "reply" none), some "triage_must_exist"),
    (ck eve (.review S K1 "reply" (some "one line offering another time")), none),     -- position 6: the call; asking is over
    (ck ann (.ask S K1 eve none), some "adviser_must_not_be_a_reviewer"),
    (ck ann (.ask S K1 fay none), some "triage_must_not_be_reviewed"),
    (ck fay (.review S K1 "ignore" none), none),                                       -- position 7: another reviewer
    (ck eve (.reply S K1 E1 none), some "only_opener_can_decide"),
    (ck ann (.reply S K3 E1 none), some "triage_must_exist"),
    (ck ann (.reply S K1 E1 (some "drafted as eml-… on the mail stream")), none),      -- position 8: decided
    (ck ann (.reply S K1 E2 none), some "triage_is_decided_once"),
    (ck ann (.ignore S K1 none), some "triage_is_decided_once"),
    (ck eve (.review S K1 "ignore" none), some "triage_must_be_undecided"),            -- nothing about K1 follows
    (ck ann (.create S K2 M2 none), none),                                             -- position 9
    (ck ann (.ask S K2 cy none), none),                                                -- position 10
    (ck ann (.ignore S K2 (some "a receipt")), none),                                  -- position 11: ignored, no advice
    (ck cy (.advise S K2 "reply" none), some "triage_must_be_undecided"),
    (ck ann (.ask S K2 dee none), some "triage_must_be_undecided"),
    (ck ann (.create S K3 M3 none), none),                                             -- position 12
    (ck ann (.ignore S K3 none), none),                                                -- position 13: alone, no ask, no review
    (ck ann (.ignore S K3 none), some "triage_is_decided_once"),
    (core ben (.streamClose S none), some "only_opener_can_close"),
    (core ann (.streamClose S none), none),
    (ck ann (.create S K2 M2 none), some "stream_must_be_open") ]                      -- nothing after a close

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
  (inbound.rules.map (·.reason) ++ ["stream_must_exist", "stream_must_be_open"]).all fun r =>
    story.any fun (_, want) => want == some r

#guard everyRuleBites

def allOk : Bool := answersOk && checksOk && everyRuleBites

end EmailTriage.Examples
