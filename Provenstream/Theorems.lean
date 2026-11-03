-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Core

/-!
# What the core guarantees

Every theorem is about a valid log (`Valid`: built by accepting candidates only) and follows from the rules that held
when its events were accepted. A layer inherits all of them: the core's events of a valid combined log form a valid
core log (`Layer.ValidX.base`, `Layer.lean`), and every event a layer adds was admitted by the core: its stream was
open and not closed (`Layer.ValidX.admitted`).

The core's one rule about people is that only the opener closes a stream (`close_by_opener`); a stream's opener and
revision are set by its opening and never change (`opener_fixed`, `opener_stays`, `proof_revision_fixed`).
-/

namespace Provenstream

/-- A rule of the list held for an accepted event. -/
theorem ok_rule {past : Past} {e : Event} (h : ok past e = true) {r : Rule} (hr : r ∈ rules) :
    r.holds (past.view e.stream) e = true :=
  (List.all_eq_true.mp h) r hr

/-! ## Minted ids are unique -/

/-- An opening in a valid log names a stream no earlier event opened. -/
theorem open_fresh {pre post : Log} {c t : Id} {u : String} {m : Meta}
    (h : Valid (pre ++ Event.streamOpened c t u m :: post)) : Past.opened pre t = false := by
  have := ok_rule h.okAt (r := streamIdMustBeNew) (by simp [rules])
  simpa [streamIdMustBeNew, Past.view, Event.stream] using this

/-- The only event that mints an id is an opening, which mints its stream's. -/
theorem minted_open {e : Event} {x : Id} (hx : x ∈ e.mintedAll) : ∃ c u m, e = .streamOpened c x u m := by
  cases e <;> simp [Event.mintedAll] at hx
  subst hx; exact ⟨_, _, _, rfl⟩

/-- An id an event mints is minted by no other event of the log, before or after it. -/
theorem minted_once {log : Log} (h : Valid log) :
    ∀ a b e x, log = a ++ e :: b → x ∈ e.mintedAll → ∀ e' ∈ a ++ b, x ∉ e'.mintedAll := by
  intro a b e x hab hx e' he' hx'
  subst hab
  obtain ⟨c, u, m, rfl⟩ := minted_open hx
  obtain ⟨c', u', m', rfl⟩ := minted_open hx'
  rcases List.mem_append.mp he' with he' | he'
  · have h1 : Past.opened a x = true := List.any_eq_true.mpr ⟨_, he', by simp [opens]⟩
    rw [open_fresh h] at h1; cases h1
  · obtain ⟨b₁, b₂, rfl⟩ := List.append_of_mem he'
    have h1 : Past.opened (a ++ Event.streamOpened c x u m :: b₁) x = true :=
      List.any_eq_true.mpr ⟨Event.streamOpened c x u m, by simp, by simp [opens]⟩
    rw [open_fresh (by simpa using h)] at h1; cases h1

/-- Two events of a valid log that mint the same id are the same event. -/
theorem minted_same {log : Log} (h : Valid log) {e₁ e₂ : Event} {x : Id}
    (h₁ : e₁ ∈ log) (h₂ : e₂ ∈ log) (hx₁ : x ∈ e₁.mintedAll) (hx₂ : x ∈ e₂.mintedAll) : e₁ = e₂ := by
  obtain ⟨a, b, rfl⟩ := List.append_of_mem h₁
  simp only [List.mem_append, List.mem_cons] at h₂
  rcases h₂ with h₂ | rfl | h₂
  · exact absurd hx₂ (minted_once h a b e₁ x rfl hx₁ e₂ (List.mem_append_left _ h₂))
  · rfl
  · exact absurd hx₂ (minted_once h a b e₁ x rfl hx₁ e₂ (List.mem_append_right _ h₂))

/-- Minting is opening: `Past.minted` is `Past.opened`. -/
theorem minted_eq_opened (L : Log) (s : Id) : Past.minted L s = Past.opened L s := by
  unfold Past.minted Past.opened
  congr 1
  funext e
  cases e with
  | streamOpened a t u m =>
    by_cases h : t = s
    · subst h; simp [Event.mintedAll, opens]
    · simp [Event.mintedAll, opens, h, Ne.symm h]
  | _ => simp [Event.mintedAll, opens]

/-- **A stream is opened once; its opener and its revision never change.** Two openings of the same stream id in a
valid log are one event: one opener, one revision. -/
theorem opener_fixed {log : Log} (h : Valid log) {t a₁ a₂ : Id} {u₁ u₂ : String} {m₁ m₂ : Meta}
    (h₁ : Event.streamOpened a₁ t u₁ m₁ ∈ log) (h₂ : Event.streamOpened a₂ t u₂ m₂ ∈ log) :
    a₁ = a₂ ∧ u₁ = u₂ := by
  have := minted_same h h₁ h₂ (x := t) (by simp [Event.mintedAll]) (by simp [Event.mintedAll])
  simp at this
  exact ⟨this.1, this.2.1⟩

/-- **A stream exists iff it was opened.** -/
theorem opened_iff (past : Past) (t : Id) :
    Past.opened past t = true ↔ ∃ a u m, Event.streamOpened a t u m ∈ past := by
  simp only [Past.opened, List.any_eq_true]
  constructor
  · rintro ⟨e, he, hc⟩
    cases e <;> simp [opens] at hc
    subst hc; exact ⟨_, _, _, he⟩
  · rintro ⟨a, u, m, he⟩; exact ⟨_, he, by simp [opens]⟩

/-- A stream's proof names a full revision. -/
theorem stream_revision_valid {pre post : Log} {t a : Id} {u : String} {m : Meta}
    (h : Valid (pre ++ Event.streamOpened a t u m :: post)) : validRevisionUrl u = true :=
  ok_rule h.okAt (r := revisionUrlMustNameACommit) (by simp [rules])

/-! ## The opener -/

/-- The opener is the actor of an opening of the stream. -/
theorem opener_mem {log : Log} {t a : Id} (h : Past.opener log t = some a) : ∃ u m, Event.streamOpened a t u m ∈ log := by
  obtain ⟨e, he, hf⟩ := List.exists_of_findSome?_eq_some h
  cases e with
  | streamOpened a' t' u m =>
    simp only [openerOf] at hf
    split at hf
    · rename_i ht; simp only [beq_iff_eq] at ht; cases hf; subst ht; exact ⟨u, m, he⟩
    · cases hf
  | _ => simp [openerOf] at hf

/-- A stream has an opener iff it was opened. -/
theorem opener_isSome (log : Log) (t : Id) : (Past.opener log t).isSome = Past.opened log t := by
  unfold Past.opener Past.opened
  induction log with
  | nil => rfl
  | cons e es ih =>
    rw [List.findSome?_cons, List.any_cons]
    cases e with
    | streamOpened a t' u m =>
      by_cases h : t' = t
      · subst h; simp [openerOf, opens]
      · simp only [openerOf, opens, beq_eq_decide, h, decide_false, Bool.false_or]; simpa [h] using ih
    | _ => simpa [openerOf, opens] using ih

/-- **Once a stream has an opener, appending anything keeps it.** No hypothesis. -/
theorem opener_stays {log : Log} {t a : Id} (h : Past.opener log t = some a) (post : Log) :
    Past.opener (log ++ post) t = some a := by
  unfold Past.opener at h ⊢
  rw [List.findSome?_append, h]; rfl

/-- In a valid log, every opening of a stream is by the stream's opener. -/
theorem opener_of_open {log : Log} (h : Valid log) {a t : Id} {u : String} {m : Meta}
    (hc : Event.streamOpened a t u m ∈ log) : Past.opener log t = some a := by
  have hs : Past.opened log t = true := (opened_iff log t).mpr ⟨a, u, m, hc⟩
  rw [← opener_isSome] at hs
  obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨u', m', hc'⟩ := opener_mem ha'
  rw [ha', (opener_fixed h hc hc').1]

/-! ## Who closes: the opener, of an open stream -/

/-- **Every close is on an open stream.** A close in a valid log names a stream opened before it and not closed. -/
theorem close_admitted {pre post : Log} {a t : Id} {m : Meta}
    (h : Valid (pre ++ Event.streamClosed a t m :: post)) :
    Past.opened pre t = true ∧ Past.closed pre t = false := by
  have hok := h.okAt
  have h1 := ok_rule hok (r := streamMustExist) (by simp [rules])
  have h2 := ok_rule hok (r := streamMustBeOpen) (by simp [rules])
  simp_all [streamMustExist, streamMustBeOpen, Past.view, Event.stream]

/-- **Only the opener closes a stream.** Every close in a valid log is by the stream's opener, as the log before it
says. -/
theorem close_by_opener {pre post : Log} {a t : Id} {m : Meta}
    (h : Valid (pre ++ Event.streamClosed a t m :: post)) : Past.opener pre t = some a := by
  have := ok_rule h.okAt (r := onlyOpenerCanClose) (by simp [rules])
  simpa [onlyOpenerCanClose, Past.view, Event.stream] using this

/-- Every event on stream `t` of a valid log means `t` was opened in that log. -/
theorem opened_of_mem {log : Log} (h : Valid log) {e : Event} (he : e ∈ log) : Past.opened log e.stream = true := by
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem he
  cases e with
  | streamOpened a t u m => simp [Past.opened, List.any_append, opens, Event.stream]
  | streamClosed a t m =>
    have := (close_admitted h).1
    simp only [Past.opened, List.any_append, Bool.or_eq_true, Event.stream] at this ⊢
    exact .inl this

/-! ## Close is final -/

/-- **Nothing is appended after a close.** In a valid log, no event after a stream's close is on that stream. -/
theorem close_final {pre mid post : Log} {a t : Id} {m : Meta} {e : Event}
    (h : Valid (pre ++ Event.streamClosed a t m :: mid ++ e :: post)) : e.stream ≠ t := by
  intro he
  have hc : Past.closed (pre ++ Event.streamClosed a t m :: mid) t = true := by
    simp [Past.closed, closes, List.any_append]
  cases e with
  | streamOpened c t' u m' =>
    simp only [Event.stream] at he; subst he
    have hp : Valid (pre ++ Event.streamClosed a t' m :: mid) :=
      Service.Valid.prefix h _ (Event.streamOpened c t' u m' :: post) (by simp)
    have ho := opened_of_mem hp (e := Event.streamClosed a t' m) (by simp)
    have := open_fresh (pre := pre ++ Event.streamClosed a t' m :: mid) (by simpa using h)
    simp only [Event.stream] at ho
    rw [this] at ho; cases ho
  | streamClosed c t' m' =>
    simp only [Event.stream] at he; subst he
    have := (close_admitted (pre := pre ++ Event.streamClosed a t' m :: mid) (by simpa using h)).2
    rw [hc] at this; cases this

/-- A stream is closed at most once. -/
theorem close_once {pre mid post : Log} {a a' t : Id} {m m' : Meta}
    (h : Valid (pre ++ Event.streamClosed a t m :: mid ++ Event.streamClosed a' t m' :: post)) : False :=
  close_final h rfl

/-! ## A stream's proof can never change; to change the proof you open a new stream -/

/-- The proof revision URL of stream `t`, if the event opened it. -/
def revisionOf (t : Id) : Event → Option String
  | .streamOpened _ t' u _ => if t' == t then some u else none
  | _ => none

/-- The proof revision URL of stream `t` in `log`: the URL its opening carries, or `none` if it was not opened. -/
def proofRevision (log : Log) (t : Id) : Option String := log.findSome? (revisionOf t)

/-- **Once a stream has a revision, appending anything keeps it.** No hypothesis. -/
theorem proof_revision_fixed {log : Log} {t : Id} {u : String} (h : proofRevision log t = some u) (post : Log) :
    proofRevision (log ++ post) t = some u := by
  unfold proofRevision at h ⊢
  rw [List.findSome?_append, h]; rfl

/-- A stream has a revision iff it was opened. -/
theorem proofRevision_isSome (log : Log) (t : Id) : (proofRevision log t).isSome = Past.opened log t := by
  unfold proofRevision Past.opened
  induction log with
  | nil => rfl
  | cons e es ih =>
    rw [List.findSome?_cons, List.any_cons]
    cases e with
    | streamOpened a t' u m =>
      by_cases h : t' = t
      · subst h; simp [revisionOf, opens]
      · simp only [revisionOf, opens, beq_eq_decide, h, decide_false, Bool.false_or]; simpa [h] using ih
    | _ => simpa [revisionOf, opens] using ih

/-- The revision is the URL of some opening of the stream. -/
theorem proofRevision_mem {log : Log} {t : Id} {u : String} (h : proofRevision log t = some u) :
    ∃ a m, Event.streamOpened a t u m ∈ log := by
  obtain ⟨e, he, hf⟩ := List.exists_of_findSome?_eq_some h
  cases e with
  | streamOpened a t' u' m =>
    simp only [revisionOf] at hf
    split at hf
    · rename_i ht; simp only [beq_iff_eq] at ht; cases hf; subst ht; exact ⟨a, m, he⟩
    · cases hf
  | _ => simp [revisionOf] at hf

/-- **In a valid log, every opening of a stream carries the stream's revision.** -/
theorem proof_revision_unique {log : Log} (h : Valid log) {a t : Id} {u : String} {m : Meta}
    (hc : Event.streamOpened a t u m ∈ log) : proofRevision log t = some u := by
  have hs : Past.opened log t = true := (opened_iff log t).mpr ⟨a, u, m, hc⟩
  rw [← proofRevision_isSome] at hs
  obtain ⟨u', hu'⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨a', m', hc'⟩ := proofRevision_mem hu'
  rw [hu', (opener_fixed h hc hc').2]

/-- **A stream's proof never changes.** -/
theorem proof_revision_stays {log post : Log} (h : Valid (log ++ post)) {t : Id} {u : String}
    (hu : proofRevision log t = some u) {a : Id} {u' : String} {m : Meta}
    (hc : Event.streamOpened a t u' m ∈ log ++ post) : u' = u := by
  have := proof_revision_unique h hc
  rw [proof_revision_fixed hu post] at this
  exact (Option.some.inj this).symm

/-- **To change the proof you open a new stream.** -/
theorem new_proof_new_stream {pre post : Log} {a t t' : Id} {u u' : String} {m : Meta}
    (h : Valid (pre ++ Event.streamOpened a t' u' m :: post)) (hu : proofRevision pre t = some u) : t' ≠ t := by
  rintro rfl
  have := proofRevision_isSome pre t'
  rw [hu, open_fresh h] at this
  cases this

theorem step_url (st : StreamState) (e : Event) : (st.step e).url = st.url.or (revisionOf st.stream e) := by
  unfold StreamState.step
  split
  · rename_i hs
    cases e with
    | streamOpened a t u m =>
      simp only [Event.stream] at hs; subst hs
      cases st.url <;> simp [keep, revisionOf]
    | _ => cases st.url <;> simp [revisionOf]
  · rename_i hs
    cases e with
    | streamOpened a t u m =>
      simp only [Event.stream] at hs
      cases st.url <;> simp [revisionOf, hs]
    | _ => cases st.url <;> simp [revisionOf]

/-- **The fast path's revision is the log's.** No hypothesis. -/
theorem fold_url (t : Id) (log : Log) : (fold t log).url = proofRevision log t :=
  fold_findSome step_url (fun _ => rfl) t log

/-!
## Not proved here (deliberately)

Everything above, the generic proofs of `Service.lean` at the core (`Core.lean`, `Streams.lean`), the wire round trips
(`Wire.lean`, `WireState.lean`) and the layer mechanism (`Layer.lean`) are about the functions `respond`, `run`,
`check`, `toEvent`, `stepJ`, `replayRows`, `entryRequest`, `entrySync` and the values they take. What follows stands
between those values and a running service, and is not proved. Each gap has an id; `docs/tcb.md` tables them.

- **gap_wire_bytes. Bytes on the wire.** Statement: the `J` value the engine decodes is the JSON line the host sent,
  and the line it prints is the `J` it computed. Proved instead: decoding inverts encoding for commands, requests,
  events, stored rows and states; whatever decodes is well formed; the engine's answer to a request is `responseToJ` of
  `respond` (`entryRequest_spec`). Not proved: our parser and printer (`Engine/Json.lean`) and the host's encoder.
- **gap_token_is_caller. The actor is the token's principal.** Statement: the `actor_id` the engine receives is the
  principal holding the bearer token (the host refuses any other, `actor_id_must_match_the_token`, and fills it in when
  absent). Proved instead: every event's actor is the request's `actor_id` (`toEvent_actor`), so every theorem about
  who acted (`close_by_opener`) is about that id. Tokens are credentials in the host's store, not events.
- **gap_principal_issuance. Principal identity and token issuance.** Statement: every principal id in the log is one
  some person or agent can authenticate as, and only they. The model has no principals of its own.
- **gap_id_collisions. Stream ids rarely collide.** Availability, not correctness: a repeated id is always refused with
  `stream_id_must_be_new` (`duplicate_refused`), and a refusal never changes the log (`refused_keeps_log`).
- **gap_storage_durability. Storage is durable and atomic.** Statement: an append the host reports is on disk, whole,
  and never changed. The store and the disks under it are outside the model.
- **gap_store_compare_and_set. The store's append is `attemptBatch`'s compare-and-set.** Statement: an append at length
  `n` commits exactly when the stream has exactly `n` rows. Proved: what follows if it does (`cas_refines_run`).
- **gap_read_decide_append. The host's glue is `attemptBatch`.** Statement: for each batch, the host syncs the stream
  into the engine up to the store's length `n`, the engine decides the requests in order, and the host appends the
  accepted events at `n` (on a failed append: forget the stream, decide again). Proved: the protocol (`cas_refines_run`,
  `batch_answer`) and the engine's bookkeeping for each step (`entryRequest_spec`, `entrySync_spec`).
- **gap_concurrency. Concurrent requests form one sequence per stream.** Proved: under any interleaving of batches with
  compare-and-set appends, each stream is `run` of its committed batches' requests (`cas_refines_run`).
- **gap_compiled_engine. The compiled engine is the proved functions.** The Lean compiler, the C compiler, the runtime,
  and the `@[extern]` primitives and `@[csimp]` replacements the functions reach (pinned by `scripts/Audit.lean`) are
  trusted.
- **gap_runtime_failures. No runtime failure changes an answer.** Checked, not proved: no constant through which
  compiled code panics is reachable from the decision and wire functions (`scripts/Audit.lean`). The parser, the
  runtime (memory, stack) and the IO loop remain.
- **gap_unproved_edge. The unproved edge does what it says.** The engine's per-stream map and message dispatch
  (`Engine/Step.lean`), its loop, and the JSON edge are not proved.
- **gap_no_unsafe_declarations. No `partial`, `unsafe`, `implemented_by`, `extern` or `native_decide` of ours.** A fact
  about declarations, checked by `scripts/Audit.lean` and the word scan, not a theorem.
- **gap_read_visibility. Who may read what.** Reads are not in the model, and the host restricts none: any
  authenticated principal reads any stream. No proof says who reads.
- **gap_engine_is_revision. The engine judging a stream was built from the stream's revision.** Proved instead: a
  stream's revision is set by its opening and never changes, whatever is appended, by the core or any layer
  (`proof_revision_fixed`, `proof_revision_unique`, `new_proof_new_stream`, `Layer.ValidX.proof_revision_unique`).
  Which binary runs is a fact about the build and the host: the host routes each stream to the engine its revision map
  lists for the revision (a commit and a package path), and checks at start that the engine reports that commit and
  package (constants written into the build by
  `scripts/stamp_revision`, trusted). `provenstream build` records the source commit and tree, the toolchain and the
  engine's sha256 in a provenance manifest; a rebuild that matches it is evidence, not proof.
- **gap_snapshot_fold. A stored snapshot is the fold of the rows it names.** Proved instead: if it is, deciding from it
  and the rows after it is deciding from the whole stream (`snapshot_sound`), and a state survives encoding
  (`stateFromJ_toJ`). The host re-folds each snapshot before trusting it.
- **gap_stream_field. The described stream field is the request's stream.** Statement: the field a schema entry names
  as its stream (`stream_id`, or the minted id it names) holds `reqStream` of the request. Not proved as a theorem; the host checks it
  on every answer (the engine reports the stream it decided on, and the host refuses an answer on another).
-/

end Provenstream
