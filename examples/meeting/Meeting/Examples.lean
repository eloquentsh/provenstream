-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Meeting.Theorems

/-!
# Worked examples: a stream of meetings, one person's

Requests with the answers they get, checked at build time (`#guard`) and compiled into the engine's `--self-test`.
Every rule of the layer and the core's admission refuse something.
-/

namespace Meeting.Examples
open Provenstream Provenstream.Layer Meeting

def url : String := "https://example.org/provenstream/tree/0123456789abcdef0123456789abcdef01234567/examples/meeting"
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

/-- A draft's URL, as the harness would name it: a text file. -/
def text (n : String) : String := s!"https://example.org/cal/{n}.md"
def D1 := text "d1"
def D2 := text "d2"
def D3 := text "d3"
def D4 := text "d4"

/-- The account a compose names. -/
def A1 : String := "gcal:ann@example.org"

/-- A pinned URL, in the blob store's form. The proof reads the pin's form and never the bytes. -/
def pinnedUrl (c : Char) : String :=
  let h := String.ofList (List.replicate 64 c)
  s!"https://blobs.example.org/b/{h}#sha256={h}&name=final.ics"

def C1 := pinnedUrl 'a'
def C2 := pinnedUrl 'b'
def C3 := pinnedUrl 'c'
def C4 := pinnedUrl 'd'
def S1 : String := "https://example.org/screens/s1"
def S2 : String := "https://example.org/screens/s2"
def S3 : String := "https://example.org/screens/s3"

/-! The forms of the fields. -/

#guard validIcsUrl C1 && pinned C1
#guard validUrl D1 && !validIcsUrl D1 && !pinned D1
#guard !pinned "https://example.org/x.ics"
#guard !pinned "https://example.org/x#sha256=abc&name=x.ics"
#guard !pinned ("https://example.org/x#sha256=" ++ String.ofList (List.replicate 64 'A') ++ "&name=x.ics")
#guard validAccount A1
#guard !validAccount "ann@example.org"
#guard !validAccount "gcal:"
#guard !validAccount "gcal:ann"
#guard !validAccount "gcal:@example.org"
#guard !validAccount "gcal:ann@"
#guard !validAccount "gcal:a@b@c"
#guard !validAccount "gcal:a b@c"

abbrev Sv := meetings.service
def core (c : Id) (cmd : Command) (f : Fresh := []) : Sv.Req := .inl (c, cmd, f)
def ck (c : Id) (cmd : MeetingCommand) (f : Fresh := []) : Sv.Req := .inr (c, cmd, f)

def story : List (Sv.Req × Option String) :=
  [ (ck ann (.create S K1 none), some "stream_must_exist"),                              -- the core's admission
    (core ann (.streamOpen url none) [S], none),
    (ck ben (.create S K1 none), some "only_opener_can_create"),
    (ck ann (.create S K1 none) [K2], some "fresh_ids_must_match_the_command"),
    (ck ann (.create S K1 (some "lunch with Dana")), none),
    (ck ann (.create S K1 none), some "meeting_id_must_be_new"),
    (ck ann (.solicit S K3 cy none), some "meeting_must_exist"),
    (ck ben (.solicit S K1 cy none), some "only_opener_can_solicit"),
    (ck ann (.solicit S K1 ann none), some "drafter_must_not_be_the_opener"),
    (ck ann (.solicit S K1 cy none), none),
    (ck ann (.solicit S K1 cy none), some "drafter_is_solicited_once"),
    (ck ann (.solicit S K1 dee none), none),
    (ck eve (.draft S K1 D1 none), some "only_solicited_drafters_can_draft"),
    (ck cy (.draft S K1 D1 none), none),
    (ck cy (.draft S K1 D2 none), none),                                                 -- as often as it likes
    (ck cy (.draft S K1 D2 none), some "urls_must_be_unique"),
    (ck dee (.draft S K1 D1 none), some "urls_must_be_unique"),                      -- another's draft
    (ck dee (.draft S K1 D3 none), none),
    (ck ann (.send S K1 C1 none), some "sent_must_be_the_latest_composed"),              -- nothing composed yet
    (ck ann (.compose S K1 C1 A1 S1 none), some "composer_must_not_be_the_opener"),
    (ck cy (.compose S K1 C1 A1 S1 none), some "composer_must_not_be_a_drafter"),
    (ck eve (.compose S K1 D2 A1 S1 none), some "urls_must_be_unique"),              -- a drafter's draft
    (ck eve (.compose S K3 C1 A1 S1 none), some "meeting_must_exist"),
    (ck eve (.compose S K1 D4 A1 S1 none), some "composed_url_must_be_pinned"),          -- no pin at all
    (ck eve (.compose S K1 C1 A1 S1 none), none),                                        -- drafting is over
    (ck ann (.solicit S K1 eve none), some "drafter_must_not_be_a_composer"),
    (ck ann (.solicit S K1 fay none), some "meeting_must_not_be_composed"),
    (ck cy (.draft S K1 D4 none), some "meeting_must_not_be_composed"),
    (ck eve (.compose S K1 C2 A1 S2 none), none),                                        -- the composer revises
    (ck fay (.compose S K1 C3 A1 S2 none), none),                                        -- another composer
    (ck eve (.send S K1 C3 none), some "only_opener_can_decide"),
    (ck ann (.send S K1 C1 none), some "sent_must_be_the_latest_composed"),              -- an earlier file
    (ck ann (.send S K1 D3 none), some "sent_must_be_the_latest_composed"),              -- a drafter's file
    (ck ann (.send S K3 C3 none), some "meeting_must_exist"),
    (ck ann (.send S K1 C3 (some "send it")), none),                                     -- decided
    (ck ann (.send S K1 C3 none), some "meeting_is_decided_once"),
    (ck ann (.discard S K1 none), some "meeting_is_decided_once"),
    (ck eve (.compose S K1 C4 A1 S3 none), some "meeting_must_be_undecided"),             -- nothing about K1 follows
    (ck ann (.create S K2 none), none),
    (ck ann (.discard S K2 (some "not needed")), none),
    (ck ann (.solicit S K2 cy none), some "meeting_must_be_undecided"),
    (ck cy (.draft S K2 D4 none), some "only_solicited_drafters_can_draft"),             -- nobody was solicited on K2
    (ck ann (.discard S K3 none), some "meeting_must_exist"),
    (core ben (.streamClose S none), some "only_opener_can_close"),
    (core ann (.streamClose S none), none),
    (ck ann (.create S K3 none), some "stream_must_be_open") ]                           -- nothing after a close

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
  (meetings.rules.map (·.reason) ++ ["stream_must_exist", "stream_must_be_open"]).all fun r =>
    story.any fun (_, want) => want == some r

#guard everyRuleBites

def allOk : Bool := answersOk && checksOk && everyRuleBites

end Meeting.Examples
