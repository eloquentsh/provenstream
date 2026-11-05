-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Email.Theorems

/-!
# Worked examples: a stream of outgoing email, one person's

Requests with the answers they get, checked at build time (`#guard`) and compiled into the engine's `--self-test`.
Every rule of the layer and the core's admission refuse something.
-/

namespace Email.Examples
open Provenstream Provenstream.Layer Email

def url : String := "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/email"
def ann : Id := "a0000000-0000-4000-8000-000000000001"   -- the opener, who sends
def ben : Id := "b0000000-0000-4000-8000-000000000002"   -- someone else on the host
def cy : Id := "c0000000-0000-4000-8000-000000000003"    -- a drafter
def dee : Id := "d0000000-0000-4000-8000-000000000004"   -- another drafter
def eve : Id := "e0000000-0000-4000-8000-000000000005"   -- a composer
def fay : Id := "f0000000-0000-4000-8000-000000000006"   -- another composer
def S : Id := "50000000-0000-7000-8000-000000000001"
def K1 : Id := "60000000-0000-7000-8000-000000000001"
def K2 : Id := "60000000-0000-7000-8000-000000000002"
def K3 : Id := "60000000-0000-7000-8000-000000000003"
def K4 : Id := "60000000-0000-7000-8000-000000000004"

/-- The .eml files, as the harness would name them. -/
def eml (n : String) : String := s!"https://example.org/mail/{n}.eml"
def IN := eml "inbound"
def D1 := eml "d1"
def D2 := eml "d2"
def D3 := eml "d3"
def D4 := eml "d4"
def C1 := eml "c1"
def C2 := eml "c2"
def C3 := eml "c3"
def C4 := eml "c4"
def C5 := eml "c5"
def OUT := eml "sent"
def OUT2 := eml "sent2"
def OUT3 := eml "sent3"
def S1 : String := "https://example.org/screens/s1"
def S2 : String := "https://example.org/screens/s2"
def S3 : String := "https://example.org/screens/s3"

abbrev Sv := outbound.service
def core (c : Id) (cmd : Command) (f : Fresh := []) : Sv.Req := .inl (c, cmd, f)
def ck (c : Id) (cmd : EmailCommand) (f : Fresh := []) : Sv.Req := .inr (c, cmd, f)

def story : List (Sv.Req × Option String) :=
  [ (ck ann (.create S K1 (some IN) none), some "stream_must_exist"),                   -- the core's admission
    (core ann (.streamOpen url none) [S], none),                                         -- position 0
    (ck ben (.create S K1 (some IN) none), some "only_opener_can_create"),
    (ck ann (.create S K1 (some IN) none) [K2], some "fresh_ids_must_match_the_command"),
    (ck ann (.create S K1 (some IN) (some "a reply to the inbound message")), none),    -- position 1: a reply
    (ck ann (.create S K1 (some IN) none), some "email_id_must_be_new"),
    (ck ann (.solicit S K3 cy none), some "email_must_exist"),
    (ck ben (.solicit S K1 cy none), some "only_opener_can_solicit"),
    (ck ann (.solicit S K1 ann none), some "drafter_must_not_be_the_opener"),
    (ck ann (.solicit S K1 cy none), none),                                              -- position 2
    (ck ann (.solicit S K1 cy none), some "drafter_is_solicited_once"),
    (ck ann (.solicit S K1 dee none), none),                                             -- position 3
    (ck eve (.draft S K1 D1 none), some "only_solicited_drafters_can_draft"),
    (ck cy (.draft S K1 IN none), some "eml_urls_must_be_unique"),                       -- the message replied to
    (ck cy (.draft S K1 D1 none), none),                                                 -- position 4
    (ck cy (.draft S K1 D2 none), none),                                                 -- position 5: as often as it likes
    (ck cy (.draft S K1 D2 none), some "eml_urls_must_be_unique"),
    (ck dee (.draft S K1 D1 none), some "eml_urls_must_be_unique"),                      -- another's draft
    (ck dee (.draft S K1 D3 none), none),                                                -- position 6
    (ck ann (.compose S K1 C1 S1 none), some "composer_must_not_be_the_opener"),
    (ck cy (.compose S K1 C1 S1 none), some "composer_must_not_be_a_drafter"),
    (ck eve (.compose S K1 D2 S1 none), some "eml_urls_must_be_unique"),                 -- a drafter's draft
    (ck eve (.compose S K3 C1 S1 none), some "email_must_exist"),
    (ck eve (.compose S K1 C1 S1 none), none),                                           -- position 7: drafting is over
    (ck ann (.solicit S K1 eve none), some "drafter_must_not_be_a_composer"),
    (ck ann (.solicit S K1 fay none), some "email_must_not_be_composed"),
    (ck cy (.draft S K1 D4 none), some "email_must_not_be_composed"),
    (ck eve (.compose S K1 C2 S2 none), none),                                           -- position 8: the composer revises
    (ck fay (.compose S K1 C3 S2 none), none),                                           -- position 9: another composer; a screen may repeat
    (ck eve (.send S K1 OUT none), some "only_opener_can_decide"),
    (ck ann (.send S K1 C2 none), some "eml_urls_must_be_unique"),                       -- a composer's draft
    (ck ann (.send S K1 D3 none), some "eml_urls_must_be_unique"),                       -- a drafter's draft
    (ck ann (.send S K1 IN none), some "eml_urls_must_be_unique"),                       -- sending the inbound message
    (ck ann (.send S K3 OUT none), some "email_must_exist"),
    (ck ann (.send S K1 OUT (some "sent from the outbox")), none),                       -- position 10: decided
    (ck ann (.send S K1 OUT2 none), some "email_is_decided_once"),
    (ck ann (.discard S K1 none), some "email_is_decided_once"),
    (ck eve (.compose S K1 C4 S3 none), some "email_must_be_undecided"),                 -- nothing about K1 follows
    (ck ann (.create S K2 none none), none),                                             -- position 11: a new email, no reply
    (ck ann (.discard S K2 (some "not worth sending")), none),                           -- position 12: discarded, nothing drafted
    (ck ann (.solicit S K2 cy none), some "email_must_be_undecided"),
    (ck cy (.draft S K2 D4 none), some "only_solicited_drafters_can_draft"),       -- nobody was solicited on K2
    (ck ann (.create S K4 (some OUT) none), none),                                       -- position 13: a reply to what K1 sent
    (ck ann (.send S K4 OUT2 none), none),                                               -- position 14: alone, no draft, no compose
    (ck ann (.discard S K3 none), some "email_must_exist"),
    (ck ann (.discard S K3 none), some "email_must_exist"),
    (core ben (.streamClose S none), some "only_opener_can_close"),
    (core ann (.streamClose S none), none),
    (ck ann (.create S K3 none none), some "stream_must_be_open") ]                      -- nothing after a close

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
  (outbound.rules.map (·.reason) ++ ["stream_must_exist", "stream_must_be_open"]).all fun r =>
    story.any fun (_, want) => want == some r

#guard everyRuleBites

def allOk : Bool := answersOk && checksOk && everyRuleBites

end Email.Examples
