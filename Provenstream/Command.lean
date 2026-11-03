-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Stream

/-!
# Commands: what a caller sends, and the event it becomes

A caller does not write events. It sends a **command**, which carries only what the caller chooses: never a minted
id. The host supplies the rest:

- the **actor** (`actor_id` on the wire), a principal id: the caller's, which the host derives from the bearer token
  (it refuses an `actor_id` that is not the token's principal, and fills it in when absent);
- the **fresh** ids, which the host mints for this request, one per id the event mints.

`toEvent` turns caller, command and fresh ids into exactly one event, or refuses before any rule runs, and `toRequest`
inverts it (`toEvent_ok_iff`).

Core Lean only.
-/

namespace Provenstream

/-- What a caller sends: one constructor per command. Each emits one event, named in the past tense (`stream.open`
`stream.opened`, `stream.close` `stream.closed`). -/
inductive Command where
  | streamOpen (url : String) («meta» : Meta)
  | streamClose (stream : Id) («meta» : Meta)
  deriving DecidableEq, Repr

/-- The ids the host minted for one request, which the event mints: `[stream]` for `stream.open`, `[]` otherwise. -/
abbrev Fresh := List Id

/-- Translate a command from caller `c` into its event; `c` is the event's actor. The one refusal here comes before
any rule: `fresh_ids_must_match_the_command`, the host supplied the wrong number of fresh ids. -/
def toEvent : Id → Command → Fresh → Except String Event
  | c, .streamOpen u m, [t] => .ok (.streamOpened c t u m)
  | c, .streamClose t m, [] => .ok (.streamClosed c t m)
  | _, _, _ => .error "fresh_ids_must_match_the_command"

/-- One request as the engine receives it: the actor (the caller), the command, the fresh ids. -/
abbrev Request := Id × Command × Fresh

/-- The request that produces an event. -/
def toRequest : Event → Request
  | .streamOpened c t u m => (c, .streamOpen u m, [t])
  | .streamClosed c t m => (c, .streamClose t m, [])

/-- The stream a request is on: the id it would mint for an opening, else the stream it names. -/
def reqStream : Request → Id
  | (_, .streamOpen .., f) => f.headD ""
  | (_, .streamClose t .., _) => t

/-- **The translation, inverted**: an event comes from a request exactly when that event's request is the request
sent. -/
theorem toEvent_ok_iff {c : Id} {cmd : Command} {f : Fresh} {e : Event} :
    toEvent c cmd f = .ok e ↔ toRequest e = (c, cmd, f) := by
  constructor
  · intro h
    cases cmd <;>
      (rcases f with _ | ⟨x, _ | ⟨y, z⟩⟩ <;> simp [toEvent] at h <;> subst h <;> rfl)
  · intro h
    cases e <;> simp [toRequest] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h <;> rfl

theorem toEvent_toRequest (e : Event) :
    toEvent (toRequest e).1 (toRequest e).2.1 (toRequest e).2.2 = .ok e := toEvent_ok_iff.mpr rfl

theorem toRequest_toEvent {c : Id} {cmd : Command} {f : Fresh} {e : Event} (h : toEvent c cmd f = .ok e) :
    toRequest e = (c, cmd, f) := toEvent_ok_iff.mp h

/-- The caller of a request is the actor of its event. -/
theorem toEvent_actor {c : Id} {cmd : Command} {f : Fresh} {e : Event} (h : toEvent c cmd f = .ok e) :
    e.actor = c := by
  have := toEvent_ok_iff.mp h
  cases e <;> simp [toRequest] at this <;> obtain ⟨rfl, -, -⟩ := this <;> rfl

/-- The ids an event mints are exactly the fresh ids the host supplied, in order. -/
theorem toEvent_minted {c : Id} {cmd : Command} {f : Fresh} {e : Event} (h : toEvent c cmd f = .ok e) :
    e.mintedAll = f := by
  have := toEvent_ok_iff.mp h
  cases e <;> simp [toRequest] at this <;> obtain ⟨-, -, rfl⟩ := this <;> rfl

theorem toEvent_stream {c : Id} {cmd : Command} {f : Fresh} {e : Event} (h : toEvent c cmd f = .ok e) :
    e.stream = reqStream (c, cmd, f) := by
  have := toEvent_ok_iff.mp h
  cases e <;> simp [toRequest] at this <;> obtain ⟨rfl, rfl, rfl⟩ := this <;> rfl

end Provenstream
