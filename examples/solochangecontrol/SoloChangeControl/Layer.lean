-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Interface

/-!
# Solo change control: a layer on the core

Software changes on one person's repository. The stream's opener creates a change and is the one who decides it;
developers (agents, or anyone else on the host) each get one branch of it and push revisions; reviewers, who are
neither developers of the change nor the opener, publish a screen and their own revision; the opener pulls, which
cuts off incoming work, and merges or abandons the change, once. Commands are intent: `merged` is final whether or not
the merge in git succeeds, and a continuation is a fresh change.

- `change.create {stream_id, change_id, from_revision_url, meta?}` → `change.created`: the opener creates a change,
  its id new on the stream, starting from a revision.
- `change.branch {stream_id, change_id, developer_id, branch_revision_url, meta?}` → `change.branched`: the opener
  hands a developer other than itself, and not a reviewer of the change, a fresh revision to push from, once per
  developer, before the pull.
- `change.push {stream_id, change_id, pushed_revision_url, meta?}` → `change.pushed`: a branched developer names a
  revision it has pushed, as often as it likes, before the pull.
- `change.pull {stream_id, change_id, meta?}` → `change.pulled`: the opener cuts off new branches and pushes, once.
  It is a prerequisite of nothing.
- `change.review {stream_id, change_id, reviewed_revision_url, screen_url, meta?}` → `change.reviewed`: anyone who
  is neither a developer of the change nor the opener names its own revision and the screen the opener should see,
  any number of times. A reviewer is never afterwards a developer of the change.
- `change.merge {stream_id, change_id, merged_revision_url, meta?}` → `change.merged`, `change.abandon {stream_id,
  change_id, meta?}` → `change.abandoned`: the opener decides the change, once; nothing about it follows.

Every revision named on a change is unique on that change (`revisions_must_be_unique`): the change's own starting
revision, each developer's branch revision, and every pushed, reviewed and merged revision differ, so each role
leaves its own revision and nobody hands back another's. A revision URL is a `url` field (`validUrl`); what it points
at, and whether it descends from the change's starting revision, is the harness's check, not the proof's.

Every permission rests on the core's `v.opener`: the opener creates, branches, pulls and decides; the developers are
whom the opener branched; the reviewers are everyone else. The memory is the notes the events make (`notes`), in
order: `("change", k, from)`, `("developer", k, developer)` and `("branch", k, branch)`, `("pushed", k, pushed)`,
`("pulled", k, "")`, `("reviewer", k, reviewer)` and `("reviewed", k, reviewed)`, `("merged", k, merged)`,
`("abandoned", k, "")`. A read of a stream adds `changes`, `developers`, `branches`, `pushed`, `pulled`, `reviewers`,
`reviewed`, `merged` and `abandoned`.
-/

namespace SoloChangeControl
open Provenstream Provenstream.Layer Provenstream.Wire

/-- A URL: a scheme, `://` and something after it; no whitespace or control character; at most 2048 characters. What
it points at is the harness's business. -/
def validUrl (s : String) : Bool :=
  s.length ≤ 2048 && s.all (fun (c : Char) => 32 < c.val && c.val != 127) &&
  match s.splitOn "://" with
  | [scheme, rest] => !scheme.isEmpty && !rest.isEmpty
  | _ => false

/-- The kind of a revision or screen field. -/
def urlKind : Kind := .text "url" validUrl

inductive ChangeCommand where
  | create (stream change : Id) (start : String) («meta» : Meta)
  | branch (stream change developer : Id) (start : String) («meta» : Meta)
  | push (stream change : Id) (pushed : String) («meta» : Meta)
  | pull (stream change : Id) («meta» : Meta)
  | review (stream change : Id) (reviewed screen : String) («meta» : Meta)
  | merge (stream change : Id) (merged : String) («meta» : Meta)
  | abandon (stream change : Id) («meta» : Meta)
  deriving DecidableEq

inductive ChangeEvent where
  | created (actor stream change : Id) (start : String) («meta» : Meta)
  | branched (actor stream change developer : Id) (start : String) («meta» : Meta)
  | pushed (actor stream change : Id) (pushed : String) («meta» : Meta)
  | pulled (actor stream change : Id) («meta» : Meta)
  | reviewed (actor stream change : Id) (reviewed screen : String) («meta» : Meta)
  | merged (actor stream change : Id) (merged : String) («meta» : Meta)
  | abandoned (actor stream change : Id) («meta» : Meta)
  deriving DecidableEq

/-- A note a change event makes: what (`change`, `developer`, `branch`, `pushed`, `pulled`, `reviewer`, `reviewed`,
`merged`, `abandoned`), the change, and whom or which (a principal, a revision URL, or `""`). -/
abbrev Note := String × String × String

def notes : ChangeEvent → List Note
  | .created _ _ k u _ => [("change", k, u)]
  | .branched _ _ k d u _ => [("developer", k, d), ("branch", k, u)]
  | .pushed _ _ k u _ => [("pushed", k, u)]
  | .pulled _ _ k _ => [("pulled", k, "")]
  | .reviewed a _ k u _ _ => [("reviewer", k, a), ("reviewed", k, u)]
  | .merged _ _ k u _ => [("merged", k, u)]
  | .abandoned _ _ k _ => [("abandoned", k, "")]

/-- The memory's step: the event's notes, appended. -/
def addNotes (st : List Note) (e : ChangeEvent) : List Note := st ++ notes e

/-- Some note says `what` of change `k`. -/
def noted (w : List Note) (what k : String) : Bool := w.any fun n => n.1 == what && n.2.1 == k

/-- The change `k` is decided: merged or abandoned. -/
def decided (w : List Note) (k : String) : Bool := noted w "merged" k || noted w "abandoned" k

/-- A note of this kind names a revision of its change. -/
def namesRevision (what : String) : Bool :=
  what == "change" || what == "branch" || what == "pushed" || what == "reviewed" || what == "merged"

/-- Some note names revision `u` of change `k`. -/
def revisionNamed (w : List Note) (k u : String) : Bool :=
  w.any fun n => namesRevision n.1 && n.2.1 == k && n.2.2 == u

/-- The changes some note says `what` of, in order. -/
def itemsOf (w : List Note) (what : String) : List String := w.filterMap fun n => if n.1 == what then some n.2.1 else none

/-- The change and the third slot of each note saying `what`, as `{change_id, <who>}`. -/
def pairsOf (w : List Note) (what who : String) : J :=
  .arr (w.filterMap fun n => if n.1 == what then some (.obj [("change_id", .str n.2.1), (who, .str n.2.2)]) else none)

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

abbrev solo : Layer where
  Cmd := ChangeCommand
  Ev := ChangeEvent
  toRequest
    | .created a t k u m => (a, .create t k u m)
    | .branched a t k d u m => (a, .branch t k d u m)
    | .pushed a t k u m => (a, .push t k u m)
    | .pulled a t k m => (a, .pull t k m)
    | .reviewed a t k u s m => (a, .review t k u s m)
    | .merged a t k u m => (a, .merge t k u m)
    | .abandoned a t k m => (a, .abandon t k m)
  ofRequest
    | (a, .create t k u m) => .created a t k u m
    | (a, .branch t k d u m) => .branched a t k d u m
    | (a, .push t k u m) => .pushed a t k u m
    | (a, .pull t k m) => .pulled a t k m
    | (a, .review t k u s m) => .reviewed a t k u s m
    | (a, .merge t k u m) => .merged a t k u m
    | (a, .abandon t k m) => .abandoned a t k m
  stream | .create t .. | .branch t .. | .push t .. | .pull t .. | .review t .. | .merge t .. | .abandon t .. => t
  schema := [{ name := "change.create", event := "change.created", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("change_id", .uuid), ("from_revision_url", urlKind), ("meta", .metaOpt)] },
             { name := "change.branch", event := "change.branched", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("change_id", .uuid), ("developer_id", .uuid),
                          ("branch_revision_url", urlKind), ("meta", .metaOpt)] },
             { name := "change.push", event := "change.pushed", who := some "a developer the opener branched",
               fields := [("stream_id", .uuid), ("change_id", .uuid), ("pushed_revision_url", urlKind), ("meta", .metaOpt)] },
             { name := "change.pull", event := "change.pulled", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("change_id", .uuid), ("meta", .metaOpt)] },
             { name := "change.review", event := "change.reviewed",
               who := some "anyone who is neither a developer of the change nor the opener",
               fields := [("stream_id", .uuid), ("change_id", .uuid), ("reviewed_revision_url", urlKind),
                          ("screen_url", urlKind), ("meta", .metaOpt)] },
             { name := "change.merge", event := "change.merged", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("change_id", .uuid), ("merged_revision_url", urlKind), ("meta", .metaOpt)] },
             { name := "change.abandon", event := "change.abandoned", who := some "the stream's opener",
               fields := [("stream_id", .uuid), ("change_id", .uuid), ("meta", .metaOpt)] }]
  toVals
    | .create t k u m => ("change.create", [.s t, .s k, .s u, .m m])
    | .branch t k d u m => ("change.branch", [.s t, .s k, .s d, .s u, .m m])
    | .push t k u m => ("change.push", [.s t, .s k, .s u, .m m])
    | .pull t k m => ("change.pull", [.s t, .s k, .m m])
    | .review t k u s m => ("change.review", [.s t, .s k, .s u, .s s, .m m])
    | .merge t k u m => ("change.merge", [.s t, .s k, .s u, .m m])
    | .abandon t k m => ("change.abandon", [.s t, .s k, .m m])
  ofVals
    | "change.create", [.s t, .s k, .s u, .m m] => some (.create t k u m)
    | "change.branch", [.s t, .s k, .s d, .s u, .m m] => some (.branch t k d u m)
    | "change.push", [.s t, .s k, .s u, .m m] => some (.push t k u m)
    | "change.pull", [.s t, .s k, .m m] => some (.pull t k m)
    | "change.review", [.s t, .s k, .s u, .s s, .m m] => some (.review t k u s m)
    | "change.merge", [.s t, .s k, .s u, .m m] => some (.merge t k u m)
    | "change.abandon", [.s t, .s k, .m m] => some (.abandon t k m)
    | _, _ => none
  memory := foldMemory [] addNotes notesToJ notesFromJ notesFromJ_toJ
  readJ st := [("changes", pairsOf st "change" "from_revision_url"),
               ("developers", pairsOf st "developer" "developer_id"),
               ("branches", pairsOf st "branch" "branch_revision_url"),
               ("pushed", pairsOf st "pushed" "pushed_revision_url"),
               ("pulled", .arr ((itemsOf st "pulled").map .str)),
               ("reviewers", pairsOf st "reviewer" "reviewer_id"),
               ("reviewed", pairsOf st "reviewed" "reviewed_revision_url"),
               ("merged", pairsOf st "merged" "merged_revision_url"),
               ("abandoned", .arr ((itemsOf st "abandoned").map .str))]
  rules := [⟨"only_opener_can_create", ["change.create"], fun v _ e => match e with
               | .created a .. => v.opener == some a | _ => true⟩,
            ⟨"change_id_must_be_new", ["change.create"], fun _ w e => match e with
               | .created _ _ k _ _ => !noted w "change" k | _ => true⟩,
            ⟨"change_must_exist", ["change.branch", "change.push", "change.pull", "change.review", "change.merge",
                                   "change.abandon"],
             fun _ w e => match e with
               | .branched _ _ k _ _ _ | .pushed _ _ k _ _ | .pulled _ _ k _ | .reviewed _ _ k _ _ _
               | .merged _ _ k _ _ | .abandoned _ _ k _ => noted w "change" k
               | _ => true⟩,
            ⟨"revisions_must_be_unique", ["change.branch", "change.push", "change.review", "change.merge"],
             fun _ w e => match e with
               | .branched _ _ k _ u _ | .pushed _ _ k u _ | .reviewed _ _ k u _ _ | .merged _ _ k u _ =>
                 !revisionNamed w k u
               | _ => true⟩,
            ⟨"only_opener_can_branch", ["change.branch"], fun v _ e => match e with
               | .branched a .. => v.opener == some a | _ => true⟩,
            ⟨"developer_must_not_be_the_opener", ["change.branch"], fun v _ e => match e with
               | .branched _ _ _ d _ _ => v.opener != some d | _ => true⟩,
            ⟨"developer_is_branched_once", ["change.branch"], fun _ w e => match e with
               | .branched _ _ k d _ _ => !w.contains ("developer", k, d) | _ => true⟩,
            ⟨"developer_must_not_be_a_reviewer", ["change.branch"], fun _ w e => match e with
               | .branched _ _ k d _ _ => !w.contains ("reviewer", k, d) | _ => true⟩,
            ⟨"change_must_not_be_pulled", ["change.branch", "change.push"], fun _ w e => match e with
               | .branched _ _ k _ _ _ | .pushed _ _ k _ _ => !noted w "pulled" k | _ => true⟩,
            ⟨"only_branched_developers_can_push", ["change.push"], fun _ w e => match e with
               | .pushed a _ k _ _ => w.contains ("developer", k, a) | _ => true⟩,
            ⟨"only_opener_can_pull", ["change.pull"], fun v _ e => match e with
               | .pulled a .. => v.opener == some a | _ => true⟩,
            ⟨"change_is_pulled_once", ["change.pull"], fun _ w e => match e with
               | .pulled _ _ k _ => !noted w "pulled" k | _ => true⟩,
            ⟨"reviewer_must_not_be_a_developer", ["change.review"], fun _ w e => match e with
               | .reviewed a _ k _ _ _ => !w.contains ("developer", k, a) | _ => true⟩,
            ⟨"reviewer_must_not_be_the_opener", ["change.review"], fun v _ e => match e with
               | .reviewed a .. => v.opener != some a | _ => true⟩,
            ⟨"only_opener_can_decide", ["change.merge", "change.abandon"], fun v _ e => match e with
               | .merged a .. | .abandoned a .. => v.opener == some a | _ => true⟩,
            ⟨"change_is_decided_once", ["change.merge", "change.abandon"], fun _ w e => match e with
               | .merged _ _ k _ _ | .abandoned _ _ k _ => !decided w k | _ => true⟩,
            ⟨"change_must_be_undecided", ["change.branch", "change.push", "change.pull", "change.review"],
             fun _ w e => match e with
               | .branched _ _ k _ _ _ | .pushed _ _ k _ _ | .pulled _ _ k _ | .reviewed _ _ k _ _ _ => !decided w k
               | _ => true⟩]

end SoloChangeControl
