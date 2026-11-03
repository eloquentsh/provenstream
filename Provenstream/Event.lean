-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
/-!
# The core's events

The two events every stream shares, one constructor each, carrying exactly that event's fields:

- `stream.opened`: the opener opens a stream, naming the proof revision that judges it for good; the opener is the
  stream's one principal the core knows;
- `stream.closed`: the opener closes the stream, finally.

An event's position in the log is its sequence number. Stream ids are minted by the host; the model needs only that a
minted id is fresh, which is a rule (`stream_id_must_be_new`). `meta` is an optional opaque string that no core rule
reads. There are no kinds, no roles and no declarations: who else may act is a layer's business.

Core Lean only.
-/

namespace Provenstream

abbrev Id := String

/-- An optional opaque string; its form (`validMeta`) is checked when it is parsed. -/
abbrev Meta := Option String

inductive Event where
  | streamOpened (actor : Id) (stream : Id) (url : String) («meta» : Meta)
  | streamClosed (actor : Id) (stream : Id) («meta» : Meta)
  deriving DecidableEq, Repr

/-- Who sent the event: every event has an actor (`actor_id` on the wire). -/
def Event.actor : Event → Id
  | .streamOpened a .. | .streamClosed a .. => a

/-- The stream an event belongs to (an opening: the stream it mints). -/
def Event.stream : Event → Id
  | .streamOpened _ t .. | .streamClosed _ t .. => t

/-- Every id an event mints. -/
def Event.mintedAll : Event → List Id
  | .streamOpened _ t .. => [t]
  | _ => []

/-! ## Forms, checked when an event is parsed -/

def isLowerHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- An id (a stream, a principal): a canonical lowercase UUID. -/
def validUuid (s : String) : Bool :=
  match s.splitOn "-" with
  | [a, b, c, d, e] =>
    a.length == 8 && b.length == 4 && c.length == 4 && d.length == 4 && e.length == 12 &&
    a.all isLowerHex && b.all isLowerHex && c.all isLowerHex && d.all isLowerHex && e.all isLowerHex
  | _ => false

/-- No control character: nothing below U+0020, and not U+007F. -/
def noControl (s : String) : Bool := s.all fun (c : Char) => 32 ≤ c.val && c.val != 127

/-- `meta`: at most 4096 bytes of UTF-8, no control character. Opaque otherwise: a layer may give it structure. -/
def validMeta (s : String) : Bool := decide (s.utf8ByteSize ≤ 4096) && noControl s

/-- An immutable revision id: 40 (SHA-1) or 64 (SHA-256) lowercase hex digits. A prefix is refused, since it could
name a revision of another repository. -/
def validRevision (s : String) : Bool := (s.length == 40 || s.length == 64) && s.all isLowerHex

/-- A segment of a package path: `[A-Za-z0-9._-]`, not empty, `.` or `..`. -/
def validSegment (seg : String) : Bool :=
  !seg.isEmpty && seg != "." && seg != ".." && seg.all fun (c : Char) => c.isAlphanum || c == '.' || c == '_' || c == '-'

/-- A package path inside a repository: one or more `/`-separated segments, each `validSegment`. -/
def validPackage (p : String) : Bool := (p.splitOn "/").all validSegment

/-- A revision URL: `<scheme>://<host>/<path>` naming a repository, then either `/commit/`, `#` or `@` and a full
revision id (the repository's root package), or `/tree/`, a full revision id, `/` and a package path (another package
of the same commit); no whitespace or control characters, at most 2048 characters. It names the revision whose rules
judge the stream. -/
def validRevisionUrl (s : String) : Bool :=
  s.length ≤ 2048 && s.all (fun (c : Char) => 32 < c.val && c.val != 127) &&
  let repoOk (repo : String) : Bool :=
    match repo.splitOn "://" with
    | [scheme, rest] =>
      !scheme.isEmpty && scheme.all (fun (c : Char) => c.isAlphanum || c == '+' || c == '-' || c == '.') &&
      (rest.splitOn "/").length ≥ 2 && (rest.splitOn "/").all (!·.isEmpty)
    | _ => false
  let split (sep : String) : Bool :=
    match s.splitOn sep with
    | [repo, rev] => repoOk repo && validRevision rev
    | _ => false
  let tree : Bool :=
    match s.splitOn "/tree/" with
    | [repo, rest] =>
      match rest.splitOn "/" with
      | rev :: seg :: segs => repoOk repo && validRevision rev && (seg :: segs).all validSegment
      | _ => false
    | _ => false
  split "/commit/" || split "#" || split "@" || tree

end Provenstream
