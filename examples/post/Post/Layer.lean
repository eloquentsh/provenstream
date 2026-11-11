-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Interface

/-!
# Post: a layer on the core

A Bluesky touch that one person sends: a post, a reply, a quote, a repost, a DM or a follow. It has the shape of `examples/meeting`. The stream's
opener creates a post and decides it. Drafters are each solicited once and hand in a text file by URL. A composer, who is
neither a drafter of the post nor the opener, hands in the final ActivityStreams 2.0 activity by pinned URL, the outbox account
and the screen. The first compose ends drafting. The opener sends or discards the post, once. Commands are intent: `sent` is
final whether or not the outbox delivers, and delivery status lives in the outbox.

- `post.create {stream_id, post_id, meta?}` -> `post.created`: the opener creates a post, its id new.
- `post.solicit {stream_id, post_id, drafter_id, meta?}` -> `post.solicited`: the opener asks a drafter other than
  itself, and not a composer of the post, once per drafter, before the first compose.
- `post.draft {stream_id, post_id, draft_url, meta?}` -> `post.drafted`: a solicited drafter hands in a URL to an
  arbitrary text file, as often as it likes, before the first compose.
- `post.compose {stream_id, post_id, composed_url, account, screen_url, meta?}` -> `post.composed`: anyone who is
  neither a drafter of the post nor the opener hands in the final file, the account and the screen. The URL ends in
  `.activity.json` and pins the file (`composed_url_must_be_pinned`). The account is a Bluesky handle. Any number of times until the
  decision. The first ends drafting.
- `post.send {stream_id, post_id, sent_url, meta?}` -> `post.sent`: the opener sends what the latest compose named
  (`sent_must_be_the_latest_composed`). `post.discard {stream_id, post_id, meta?}` -> `post.discarded`. Once.

The stream holds no file text. An engine cannot fetch a URL, so this proof cannot see a file's contents. It checks the form
of the pin and nothing about the bytes. So every sent URL carries a pin (`every_sent_file_is_pinned`), and whoever reads the
URL checks the bytes against that pin. The harness does that, and runs the outbox's own check, before it submits anything.

Every URL a drafter or composer names is unique on its post (`urls_must_be_unique`). So a composed URL names one account
for good. A sent URL repeats a composed one by design.

The memory is the notes the events make: `("post", k, "")`, `("drafter", k, drafter)`, `("draft", k, u)`, `("composer", k,
composer)` and `("composed", k, u)`, `("sent", k, u)`, `("discarded", k, "")`. A read of a stream adds `posts`, `drafters`,
`drafts`, `composers`, `composed`, `sent` and `discarded`.
-/

namespace Post
open Provenstream Provenstream.Layer Provenstream.Wire

/-- A URL: a scheme, `://` and something after it; no whitespace or control character; at most 2048 characters. What
it points at is the harness's business. -/
def validUrl (s : String) : Bool :=
  s.length ≤ 2048 && s.all (fun (c : Char) => 32 < c.val && c.val != 127) &&
  match s.splitOn "://" with
  | [scheme, rest] => !scheme.isEmpty && !rest.isEmpty
  | _ => false

/-- The URL of an activity: a URL whose last fourteen characters are `.activity.json`. The file inside is ActivityStreams 2.0. The
ending is this proof's name for it, as `.eml` and `.ics` name theirs. (Spelled on the character list rather than with
`String.endsWith`, whose compiled form reaches primitives the audit does not trust.) -/
def endsWithActivity (s : String) : Bool :=
  match s.toList.reverse with
  | 'n' :: 'o' :: 's' :: 'j' :: '.' :: 'y' :: 't' :: 'i' :: 'v' :: 'i' :: 't' :: 'c' :: 'a' :: '.' :: _ => true
  | _ => false

def validActivityUrl (s : String) : Bool := validUrl s && endsWithActivity s

/-- No two dots side by side. -/
def noDoubleDot : List Char → Bool
  | '.' :: '.' :: _ => false
  | _ :: rest => noDoubleDot rest
  | [] => true

/-- An outbox account: a Bluesky handle. Lower case letters, digits, hyphens and dots, at most 253 characters, at least one
dot, no empty label. (Spelled on the character list, as `endsWithActivity` is.) -/
def isHandleChar (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == '-' || c == '.'

def validAccount (s : String) : Bool :=
  let cs := s.toList
  cs.length ≤ 253 && cs.all isHandleChar && (cs.filter (· == '.')).length ≥ 1 &&
  cs.head? != some '.' && cs.getLast? != some '.' && noDoubleDot cs

/-- The kind of a draft's URL or a screen's: any URL. -/
def urlKind : Kind := .text "url" validUrl

/-- The kind of an activity URL field: the composed file, the sent file. -/
def activityKind : Kind := .text "activity" validActivityUrl

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

inductive PostCommand where
  | create (stream post : Id) («meta» : Meta)
  | solicit (stream post drafter : Id) («meta» : Meta)
  | draft (stream post : Id) (draft : String) («meta» : Meta)
  | compose (stream post : Id) (composed account screen : String) («meta» : Meta)
  | send (stream post : Id) (sent : String) («meta» : Meta)
  | discard (stream post : Id) («meta» : Meta)
  deriving DecidableEq

inductive PostEvent where
  | created (actor stream post : Id) («meta» : Meta)
  | solicited (actor stream post drafter : Id) («meta» : Meta)
  | drafted (actor stream post : Id) (draft : String) («meta» : Meta)
  | composed (actor stream post : Id) (composed account screen : String) («meta» : Meta)
  | sent (actor stream post : Id) (sent : String) («meta» : Meta)
  | discarded (actor stream post : Id) («meta» : Meta)
  deriving DecidableEq

/-- A note a post event makes: what (`post`, `drafter`, `draft`, `composer`, `composed`, `sent`, `discarded`), the
post, and whom or which (a principal, a URL, or `""`). -/
abbrev Note := String × String × String

def notes : PostEvent → List Note
  | .created _ _ k _ => [("post", k, "")]
  | .solicited _ _ k d _ => [("drafter", k, d)]
  | .drafted _ _ k u _ => [("draft", k, u)]
  | .composed a _ k u _ _ _ => [("composer", k, a), ("composed", k, u)]
  | .sent _ _ k u _ => [("sent", k, u)]
  | .discarded _ _ k _ => [("discarded", k, "")]

/-- The memory's step: the event's notes, appended. -/
def addNotes (st : List Note) (e : PostEvent) : List Note := st ++ notes e

/-- Some note says `what` of post `k`. -/
def noted (w : List Note) (what k : String) : Bool := w.any fun n => n.1 == what && n.2.1 == k

/-- The post `k` is decided: sent or discarded. -/
def decided (w : List Note) (k : String) : Bool := noted w "sent" k || noted w "discarded" k

/-- A note of this kind names a file of its post. -/
def namesUrl (what : String) : Bool :=
  what == "draft" || what == "composed"

/-- Some note names the URL `u` of post `k`. -/
def urlNamed (w : List Note) (k u : String) : Bool :=
  w.any fun n => namesUrl n.1 && n.2.1 == k && n.2.2 == u

/-- The URL of the latest compose of post `k`, if any. -/
def lastComposed (w : List Note) (k : String) : Option String :=
  w.foldl (fun acc n => if n.1 == "composed" && n.2.1 == k then some n.2.2 else acc) none

/-- The posts some note says `what` of, in order. -/
def itemsOf (w : List Note) (what : String) : List String := w.filterMap fun n => if n.1 == what then some n.2.1 else none

/-- The post and the third slot of each note saying `what`, as `{post_id, <who>}`. -/
def pairsOf (w : List Note) (what who : String) : J :=
  .arr (w.filterMap fun n => if n.1 == what then some (.obj [("post_id", .str n.2.1), (who, .str n.2.2)]) else none)

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

abbrev posts : Layer where
  Cmd := PostCommand
  Ev := PostEvent
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
  schema := [{ name := "post.create", event := "post.created", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("post_id", .uuid), ("meta", .metaOpt)] },
             { name := "post.solicit", event := "post.solicited", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("post_id", .uuid), ("drafter_id", .uuid), ("meta", .metaOpt)] },
             { name := "post.draft", event := "post.drafted", who := some "a drafter the opener solicited",
               fields := [("stream_id", .uuid), ("post_id", .uuid), ("draft_url", urlKind), ("meta", .metaOpt)] },
             { name := "post.compose", event := "post.composed",
               who := some "anyone who is neither a drafter of the post nor the opener",
               fields := [("stream_id", .uuid), ("post_id", .uuid), ("composed_url", activityKind),
                          ("account", accountKind), ("screen_url", urlKind), ("meta", .metaOpt)] },
             { name := "post.send", event := "post.sent", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("post_id", .uuid), ("sent_url", activityKind), ("meta", .metaOpt)] },
             { name := "post.discard", event := "post.discarded", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("post_id", .uuid), ("meta", .metaOpt)] }]
  toVals
    | .create t k m => ("post.create", [.s t, .s k, .m m])
    | .solicit t k d m => ("post.solicit", [.s t, .s k, .s d, .m m])
    | .draft t k u m => ("post.draft", [.s t, .s k, .s u, .m m])
    | .compose t k u x s m => ("post.compose", [.s t, .s k, .s u, .s x, .s s, .m m])
    | .send t k u m => ("post.send", [.s t, .s k, .s u, .m m])
    | .discard t k m => ("post.discard", [.s t, .s k, .m m])
  ofVals
    | "post.create", [.s t, .s k, .m m] => some (.create t k m)
    | "post.solicit", [.s t, .s k, .s d, .m m] => some (.solicit t k d m)
    | "post.draft", [.s t, .s k, .s u, .m m] => some (.draft t k u m)
    | "post.compose", [.s t, .s k, .s u, .s x, .s s, .m m] => some (.compose t k u x s m)
    | "post.send", [.s t, .s k, .s u, .m m] => some (.send t k u m)
    | "post.discard", [.s t, .s k, .m m] => some (.discard t k m)
    | _, _ => none
  memory := foldMemory [] addNotes notesToJ notesFromJ notesFromJ_toJ
  readJ st := [("posts", .arr ((itemsOf st "post").map .str)),
               ("drafters", pairsOf st "drafter" "drafter_id"),
               ("drafts", pairsOf st "draft" "draft_url"),
               ("composers", pairsOf st "composer" "composer_id"),
               ("composed", pairsOf st "composed" "composed_url"),
               ("sent", pairsOf st "sent" "sent_url"),
               ("discarded", .arr ((itemsOf st "discarded").map .str))]
  rules := [⟨"only_opener_can_create", ["post.create"], fun v _ e => match e with
               | .created a .. => v.opener == some a | _ => true⟩,
            ⟨"post_id_must_be_new", ["post.create"], fun _ w e => match e with
               | .created _ _ k _ => !noted w "post" k | _ => true⟩,
            ⟨"post_must_exist", ["post.solicit", "post.draft", "post.compose", "post.send", "post.discard"],
             fun _ w e => match e with
               | .solicited _ _ k _ _ | .drafted _ _ k _ _ | .composed _ _ k _ _ _ _ | .sent _ _ k _ _
               | .discarded _ _ k _ => noted w "post" k
               | _ => true⟩,
            ⟨"urls_must_be_unique", ["post.draft", "post.compose"],
             fun _ w e => match e with
               | .drafted _ _ k u _ | .composed _ _ k u _ _ _ => !urlNamed w k u
               | _ => true⟩,
            ⟨"composed_url_must_be_pinned", ["post.compose"], fun _ _ e => match e with
               | .composed _ _ _ u _ _ _ => pinned u | _ => true⟩,
            ⟨"only_opener_can_solicit", ["post.solicit"], fun v _ e => match e with
               | .solicited a .. => v.opener == some a | _ => true⟩,
            ⟨"drafter_must_not_be_the_opener", ["post.solicit"], fun v _ e => match e with
               | .solicited _ _ _ d _ => v.opener != some d | _ => true⟩,
            ⟨"drafter_is_solicited_once", ["post.solicit"], fun _ w e => match e with
               | .solicited _ _ k d _ => !w.contains ("drafter", k, d) | _ => true⟩,
            ⟨"drafter_must_not_be_a_composer", ["post.solicit"], fun _ w e => match e with
               | .solicited _ _ k d _ => !w.contains ("composer", k, d) | _ => true⟩,
            ⟨"post_must_not_be_composed", ["post.solicit", "post.draft"], fun _ w e => match e with
               | .solicited _ _ k _ _ | .drafted _ _ k _ _ => !noted w "composed" k | _ => true⟩,
            ⟨"only_solicited_drafters_can_draft", ["post.draft"], fun _ w e => match e with
               | .drafted a _ k _ _ => w.contains ("drafter", k, a) | _ => true⟩,
            ⟨"composer_must_not_be_a_drafter", ["post.compose"], fun _ w e => match e with
               | .composed a _ k _ _ _ _ => !w.contains ("drafter", k, a) | _ => true⟩,
            ⟨"composer_must_not_be_the_opener", ["post.compose"], fun v _ e => match e with
               | .composed a .. => v.opener != some a | _ => true⟩,
            ⟨"sent_must_be_the_latest_composed", ["post.send"], fun _ w e => match e with
               | .sent _ _ k u _ => lastComposed w k == some u | _ => true⟩,
            ⟨"only_opener_can_decide", ["post.send", "post.discard"], fun v _ e => match e with
               | .sent a .. | .discarded a .. => v.opener == some a | _ => true⟩,
            ⟨"post_is_decided_once", ["post.send", "post.discard"], fun _ w e => match e with
               | .sent _ _ k _ _ | .discarded _ _ k _ => !decided w k | _ => true⟩,
            ⟨"post_must_be_undecided", ["post.solicit", "post.draft", "post.compose"],
             fun _ w e => match e with
               | .solicited _ _ k _ _ | .drafted _ _ k _ _ | .composed _ _ k _ _ _ _ => !decided w k | _ => true⟩]

end Post
