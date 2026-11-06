-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Interface

/-!
# Meeting: a layer on the core

A calendar meeting that one person sends: a new event, an update, a cancel or an RSVP. It has the shape of `examples/email`.
The stream's opener creates a meeting and decides it. Drafters are each solicited once and hand in a text file by URL. A
composer, who is neither a drafter of the meeting nor the opener, hands in the final `.ics` by pinned URL, the outbox account
and the screen. The first compose ends drafting. The opener sends or discards the meeting, once. Commands are intent: `sent`
is final whether or not the outbox delivers, and delivery status lives in the outbox.

- `meeting.create {stream_id, meeting_id, meta?}` -> `meeting.created`: the opener creates a meeting, its id new.
- `meeting.solicit {stream_id, meeting_id, drafter_id, meta?}` -> `meeting.solicited`: the opener asks a drafter other than
  itself, and not a composer of the meeting, once per drafter, before the first compose.
- `meeting.draft {stream_id, meeting_id, draft_url, meta?}` -> `meeting.drafted`: a solicited drafter hands in a URL to an
  arbitrary text file, as often as it likes, before the first compose.
- `meeting.compose {stream_id, meeting_id, composed_url, account, screen_url, meta?}` -> `meeting.composed`: anyone who is
  neither a drafter of the meeting nor the opener hands in the final file, the account and the screen. The URL ends in
  `.ics` and pins the file (`composed_url_must_be_pinned`). The account has the form `gcal:<email>`. Any number of times
  until the decision. The first ends drafting.
- `meeting.send {stream_id, meeting_id, sent_url, meta?}` -> `meeting.sent`: the opener sends what the latest compose named
  (`sent_must_be_the_latest_composed`). `meeting.discard {stream_id, meeting_id, meta?}` -> `meeting.discarded`. Once.

The stream holds no file text. An engine cannot fetch a URL, so this proof cannot see a file's contents. It checks the form
of the pin and nothing about the bytes. So every sent URL carries a pin (`every_sent_file_is_pinned`), and whoever reads the
URL checks the bytes against that pin. The outbox's watcher does that, and parses the file, before anything can go out.

Every URL a drafter or composer names is unique on its meeting (`urls_must_be_unique`). So a composed URL names one account
for good. A sent URL repeats a composed one by design.

The memory is the notes the events make: `("meeting", k, "")`, `("drafter", k, drafter)`, `("draft", k, u)`, `("composer", k,
composer)` and `("composed", k, u)`, `("sent", k, u)`, `("discarded", k, "")`. A read of a stream adds `meetings`, `drafters`,
`drafts`, `composers`, `composed`, `sent` and `discarded`.
-/

namespace Meeting
open Provenstream Provenstream.Layer Provenstream.Wire

/-- A URL: a scheme, `://` and something after it; no whitespace or control character; at most 2048 characters. What
it points at is the harness's business. -/
def validUrl (s : String) : Bool :=
  s.length ≤ 2048 && s.all (fun (c : Char) => 32 < c.val && c.val != 127) &&
  match s.splitOn "://" with
  | [scheme, rest] => !scheme.isEmpty && !rest.isEmpty
  | _ => false

/-- The URL of an `.ics`: a URL whose last four characters are `.ics`. (Spelled on the character list rather than
with `String.endsWith`, whose compiled form reaches primitives the audit does not trust.) -/
def endsWithIcs (s : String) : Bool :=
  match s.toList.reverse with
  | 's' :: 'c' :: 'i' :: '.' :: _ => true
  | _ => false

def validIcsUrl (s : String) : Bool := validUrl s && endsWithIcs s

/-- An outbox account: `gcal:`, then one address of at most 320 characters with one `@` inside it. (Spelled on the
character list, as `endsWithIcs` is.) -/
def validAccount (s : String) : Bool :=
  match s.toList with
  | 'g' :: 'c' :: 'a' :: 'l' :: ':' :: rest =>
    rest.length ≤ 320 && rest.all (fun (c : Char) => 32 < c.val && c.val != 127) &&
    (rest.filter (· == '@')).length == 1 && rest.head? != some '@' && rest.getLast? != some '@'
  | _ => false

/-- The kind of a draft's URL or a screen's: any URL. -/
def urlKind : Kind := .text "url" validUrl

/-- The kind of an `.ics` URL field: the composed file, the sent file. -/
def icsKind : Kind := .text "ics" validIcsUrl

/-- The kind of the account a compose names. -/
def accountKind : Kind := .text "account" validAccount

/-- The hex digits of a pin. -/
def isLowerHex (c : Char) : Bool := ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

/-- The characters before the first `&`. -/
def beforeAmp : List Char → List Char
  | [] => []
  | c :: cs => if c == '&' then [] else c :: beforeAmp cs

/-- The sha256 a URL pins: the 64 hex digits after `#sha256=`, up to `&` or the end. -/
def pinOf (u : String) : Option String :=
  match (u.toList.dropWhile (· != '#')) with
  | '#' :: 's' :: 'h' :: 'a' :: '2' :: '5' :: '6' :: '=' :: rest =>
    let h := beforeAmp rest
    if h.length == 64 && h.all isLowerHex then some (String.ofList h) else none
  | _ => none

/-- The URL carries a pin. This is the form of the pin alone: the proof never sees the bytes. -/
def pinned (u : String) : Bool :=
  match pinOf u with
  | some _ => true
  | none => false

inductive MeetingCommand where
  | create (stream meeting : Id) («meta» : Meta)
  | solicit (stream meeting drafter : Id) («meta» : Meta)
  | draft (stream meeting : Id) (draft : String) («meta» : Meta)
  | compose (stream meeting : Id) (composed account screen : String) («meta» : Meta)
  | send (stream meeting : Id) (sent : String) («meta» : Meta)
  | discard (stream meeting : Id) («meta» : Meta)
  deriving DecidableEq

inductive MeetingEvent where
  | created (actor stream meeting : Id) («meta» : Meta)
  | solicited (actor stream meeting drafter : Id) («meta» : Meta)
  | drafted (actor stream meeting : Id) (draft : String) («meta» : Meta)
  | composed (actor stream meeting : Id) (composed account screen : String) («meta» : Meta)
  | sent (actor stream meeting : Id) (sent : String) («meta» : Meta)
  | discarded (actor stream meeting : Id) («meta» : Meta)
  deriving DecidableEq

/-- A note a meeting event makes: what (`meeting`, `drafter`, `draft`, `composer`, `composed`, `sent`, `discarded`), the
meeting, and whom or which (a principal, a URL, or `""`). -/
abbrev Note := String × String × String

def notes : MeetingEvent → List Note
  | .created _ _ k _ => [("meeting", k, "")]
  | .solicited _ _ k d _ => [("drafter", k, d)]
  | .drafted _ _ k u _ => [("draft", k, u)]
  | .composed a _ k u _ _ _ => [("composer", k, a), ("composed", k, u)]
  | .sent _ _ k u _ => [("sent", k, u)]
  | .discarded _ _ k _ => [("discarded", k, "")]

/-- The memory's step: the event's notes, appended. -/
def addNotes (st : List Note) (e : MeetingEvent) : List Note := st ++ notes e

/-- Some note says `what` of meeting `k`. -/
def noted (w : List Note) (what k : String) : Bool := w.any fun n => n.1 == what && n.2.1 == k

/-- The meeting `k` is decided: sent or discarded. -/
def decided (w : List Note) (k : String) : Bool := noted w "sent" k || noted w "discarded" k

/-- A note of this kind names a file of its meeting. -/
def namesUrl (what : String) : Bool :=
  what == "draft" || what == "composed"

/-- Some note names the URL `u` of meeting `k`. -/
def urlNamed (w : List Note) (k u : String) : Bool :=
  w.any fun n => namesUrl n.1 && n.2.1 == k && n.2.2 == u

/-- The URL of the latest compose of meeting `k`, if any. -/
def lastComposed (w : List Note) (k : String) : Option String :=
  w.foldl (fun acc n => if n.1 == "composed" && n.2.1 == k then some n.2.2 else acc) none

/-- The meetings some note says `what` of, in order. -/
def itemsOf (w : List Note) (what : String) : List String := w.filterMap fun n => if n.1 == what then some n.2.1 else none

/-- The meeting and the third slot of each note saying `what`, as `{meeting_id, <who>}`. -/
def pairsOf (w : List Note) (what who : String) : J :=
  .arr (w.filterMap fun n => if n.1 == what then some (.obj [("meeting_id", .str n.2.1), (who, .str n.2.2)]) else none)

def notesToJ (st : List Note) : J := .arr (st.map fun (f, k, q) => .arr [.str f, .str k, .str q])

def notesFromJ : J → Except String (List Note)
  | .arr xs => xs.mapM fun
    | .arr [.str f, .str k, .str q] => .ok (f, k, q)
    | _ => .error "state: expected a note"
  | _ => .error "state: expected notes"

theorem notesFromJ_toJ (st : List Note) : notesFromJ (notesToJ st) = .ok st := by
  induction st with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨f, k, q⟩ := x
    simp only [notesToJ, notesFromJ, List.map_cons, List.mapM_cons] at ih ⊢
    simp [ih, bind, Except.bind, pure, Except.pure]

abbrev meetings : Layer where
  Cmd := MeetingCommand
  Ev := MeetingEvent
  toRequest
    | .created a t k m => (a, .create t k m)
    | .solicited a t k d m => (a, .solicit t k d m)
    | .drafted a t k u m => (a, .draft t k u m)
    | .composed a t k u x s m => (a, .compose t k u x s m)
    | .sent a t k u m => (a, .send t k u m)
    | .discarded a t k m => (a, .discard t k m)
  ofRequest
    | (a, .create t k m) => .created a t k m
    | (a, .solicit t k d m) => .solicited a t k d m
    | (a, .draft t k u m) => .drafted a t k u m
    | (a, .compose t k u x s m) => .composed a t k u x s m
    | (a, .send t k u m) => .sent a t k u m
    | (a, .discard t k m) => .discarded a t k m
  stream | .create t .. | .solicit t .. | .draft t .. | .compose t .. | .send t .. | .discard t .. => t
  schema := [{ name := "meeting.create", event := "meeting.created", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("meeting_id", .uuid), ("meta", .metaOpt)] },
             { name := "meeting.solicit", event := "meeting.solicited", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("meeting_id", .uuid), ("drafter_id", .uuid), ("meta", .metaOpt)] },
             { name := "meeting.draft", event := "meeting.drafted", who := some "a drafter the opener solicited",
               fields := [("stream_id", .uuid), ("meeting_id", .uuid), ("draft_url", urlKind), ("meta", .metaOpt)] },
             { name := "meeting.compose", event := "meeting.composed",
               who := some "anyone who is neither a drafter of the meeting nor the opener",
               fields := [("stream_id", .uuid), ("meeting_id", .uuid), ("composed_url", icsKind),
                          ("account", accountKind), ("screen_url", urlKind), ("meta", .metaOpt)] },
             { name := "meeting.send", event := "meeting.sent", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("meeting_id", .uuid), ("sent_url", icsKind), ("meta", .metaOpt)] },
             { name := "meeting.discard", event := "meeting.discarded", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("meeting_id", .uuid), ("meta", .metaOpt)] }]
  toVals
    | .create t k m => ("meeting.create", [.s t, .s k, .m m])
    | .solicit t k d m => ("meeting.solicit", [.s t, .s k, .s d, .m m])
    | .draft t k u m => ("meeting.draft", [.s t, .s k, .s u, .m m])
    | .compose t k u x s m => ("meeting.compose", [.s t, .s k, .s u, .s x, .s s, .m m])
    | .send t k u m => ("meeting.send", [.s t, .s k, .s u, .m m])
    | .discard t k m => ("meeting.discard", [.s t, .s k, .m m])
  ofVals
    | "meeting.create", [.s t, .s k, .m m] => some (.create t k m)
    | "meeting.solicit", [.s t, .s k, .s d, .m m] => some (.solicit t k d m)
    | "meeting.draft", [.s t, .s k, .s u, .m m] => some (.draft t k u m)
    | "meeting.compose", [.s t, .s k, .s u, .s x, .s s, .m m] => some (.compose t k u x s m)
    | "meeting.send", [.s t, .s k, .s u, .m m] => some (.send t k u m)
    | "meeting.discard", [.s t, .s k, .m m] => some (.discard t k m)
    | _, _ => none
  memory := foldMemory [] addNotes notesToJ notesFromJ notesFromJ_toJ
  readJ st := [("meetings", .arr ((itemsOf st "meeting").map .str)),
               ("drafters", pairsOf st "drafter" "drafter_id"),
               ("drafts", pairsOf st "draft" "draft_url"),
               ("composers", pairsOf st "composer" "composer_id"),
               ("composed", pairsOf st "composed" "composed_url"),
               ("sent", pairsOf st "sent" "sent_url"),
               ("discarded", .arr ((itemsOf st "discarded").map .str))]
  rules := [⟨"only_opener_can_create", ["meeting.create"], fun v _ e => match e with
               | .created a .. => v.opener == some a | _ => true⟩,
            ⟨"meeting_id_must_be_new", ["meeting.create"], fun _ w e => match e with
               | .created _ _ k _ => !noted w "meeting" k | _ => true⟩,
            ⟨"meeting_must_exist", ["meeting.solicit", "meeting.draft", "meeting.compose", "meeting.send", "meeting.discard"],
             fun _ w e => match e with
               | .solicited _ _ k _ _ | .drafted _ _ k _ _ | .composed _ _ k _ _ _ _ | .sent _ _ k _ _
               | .discarded _ _ k _ => noted w "meeting" k
               | _ => true⟩,
            ⟨"urls_must_be_unique", ["meeting.draft", "meeting.compose"],
             fun _ w e => match e with
               | .drafted _ _ k u _ | .composed _ _ k u _ _ _ => !urlNamed w k u
               | _ => true⟩,
            ⟨"composed_url_must_be_pinned", ["meeting.compose"], fun _ _ e => match e with
               | .composed _ _ _ u _ _ _ => pinned u | _ => true⟩,
            ⟨"only_opener_can_solicit", ["meeting.solicit"], fun v _ e => match e with
               | .solicited a .. => v.opener == some a | _ => true⟩,
            ⟨"drafter_must_not_be_the_opener", ["meeting.solicit"], fun v _ e => match e with
               | .solicited _ _ _ d _ => v.opener != some d | _ => true⟩,
            ⟨"drafter_is_solicited_once", ["meeting.solicit"], fun _ w e => match e with
               | .solicited _ _ k d _ => !w.contains ("drafter", k, d) | _ => true⟩,
            ⟨"drafter_must_not_be_a_composer", ["meeting.solicit"], fun _ w e => match e with
               | .solicited _ _ k d _ => !w.contains ("composer", k, d) | _ => true⟩,
            ⟨"meeting_must_not_be_composed", ["meeting.solicit", "meeting.draft"], fun _ w e => match e with
               | .solicited _ _ k _ _ | .drafted _ _ k _ _ => !noted w "composed" k | _ => true⟩,
            ⟨"only_solicited_drafters_can_draft", ["meeting.draft"], fun _ w e => match e with
               | .drafted a _ k _ _ => w.contains ("drafter", k, a) | _ => true⟩,
            ⟨"composer_must_not_be_a_drafter", ["meeting.compose"], fun _ w e => match e with
               | .composed a _ k _ _ _ _ => !w.contains ("drafter", k, a) | _ => true⟩,
            ⟨"composer_must_not_be_the_opener", ["meeting.compose"], fun v _ e => match e with
               | .composed a .. => v.opener != some a | _ => true⟩,
            ⟨"sent_must_be_the_latest_composed", ["meeting.send"], fun _ w e => match e with
               | .sent _ _ k u _ => lastComposed w k == some u | _ => true⟩,
            ⟨"only_opener_can_decide", ["meeting.send", "meeting.discard"], fun v _ e => match e with
               | .sent a .. | .discarded a .. => v.opener == some a | _ => true⟩,
            ⟨"meeting_is_decided_once", ["meeting.send", "meeting.discard"], fun _ w e => match e with
               | .sent _ _ k _ _ | .discarded _ _ k _ => !decided w k | _ => true⟩,
            ⟨"meeting_must_be_undecided", ["meeting.solicit", "meeting.draft", "meeting.compose"],
             fun _ w e => match e with
               | .solicited _ _ k _ _ | .drafted _ _ k _ _ | .composed _ _ k _ _ _ _ => !decided w k | _ => true⟩]

end Meeting
