-- Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
-- SPDX-License-Identifier: MIT
import Provenstream.Theorems

/-!
# Commands become events; one log per stream; compare-and-set appends

The theorems about `respond` and `run` at the core, from `Service.lean`, and the two facts that use the core's rules:
a repeated id is refused and never stored (`duplicate_refused`), and an opening's id is fresh exactly when its stream
has no event (`stream_id_new_iff_stream_empty`).
-/

namespace Provenstream

/-- An answer is an acceptance exactly when the translation succeeds and every rule holds against the log before it. -/
theorem respond_accepted_iff {log : Log} {r : Request} {e : Event} :
    respond log r = .accepted e ↔ toEvent r.1 r.2.1 r.2.2 = .ok e ∧ ok log e = true :=
  Service.respond_accepted_iff (S := coreService)

/-- A refusal leaves the log exactly as it was. -/
theorem refused_keeps_log {log : Log} {r : Request} {x : String} (h : respond log r = .rejected x) :
    (runFrom log [r]).1 = log := by
  have := Service.runFrom_one (S := coreService) log r
  simp only [runFrom] at this ⊢
  rw [this]; simp [respond] at h ⊢; simp [h]

/-- **A repeated id is refused, never stored.** If a fresh id the host supplies was minted before, the request is
refused with `stream_id_must_be_new`, whatever else it says. A UUID collision costs a refusal, never a change to the log. -/
theorem duplicate_refused {log : Log} {c : Id} {cmd : Command} {f : Fresh} {e : Event} {x : Id}
    (h : toEvent c cmd f = .ok e) (hx : x ∈ f) (hm : Past.minted log x = true) :
    respond log (c, cmd, f) = .rejected "stream_id_must_be_new" := by
  rw [← toEvent_minted h] at hx
  obtain ⟨c', u, m, rfl⟩ := minted_open hx
  rw [minted_eq_opened] at hm
  have hr : rejection log (.streamOpened c' x u m) = some "stream_id_must_be_new" := by
    simp [rejection, View.rejection, rules, streamIdMustBeNew, Past.view, Event.stream, hm]
  exact (Service.respond_rejected_iff (S := coreService)).mpr (.inr ⟨_, h, hr⟩)

/-- The log `run` produces is valid. -/
theorem run_valid (reqs : List Request) : Valid (run reqs).1 := Service.run_valid (S := coreService) reqs

/-- **Every valid log is produced.** Every valid log is what `run` produces from one request per event, all accepted. -/
theorem run_total {log : Log} (h : Valid log) : run (log.map toRequest) = (log, log.map Response.accepted) :=
  Service.run_total h

/-- **A valid event log and the commands that produce it determine each other.** -/
theorem commands_events_bijection :
    (∀ log, Valid log → AllAccepted (toRequests log) ∧ (run (toRequests log)).1 = log) ∧
    (∀ reqs, AllAccepted reqs → Valid (run reqs).1 ∧ toRequests (run reqs).1 = reqs) :=
  Service.commands_events_bijection (S := coreService)

/-- The answer to a request against the whole log is its answer against its stream's events. -/
theorem respond_local (L : Log) (r : Request) : respond (onStream L (reqStream r)) r = respond L r :=
  Service.respond_local (S := coreService) L r

/-- **A stream's log is `run` of its own requests.** -/
theorem run_project (reqs : List Request) (s : Id) :
    onStream (run reqs).1 s = (run (reqs.filter (reqStream · == s))).1 ∧
    ((reqs.zip (run reqs).2).filter (reqStream ·.1 == s)).map (·.2) = (run (reqs.filter (reqStream · == s))).2 :=
  Service.run_project (S := coreService) reqs s

/-- **Compare-and-set batch appends refine `run`.** Under any interleaving of validators, every stream holds exactly
`run` of the requests of the batches that committed on it, in commit order, and the answers delivered are `run`'s. -/
theorem cas_refines_run (atts : List (Id × List Request × Nat)) (s : Id) :
    (execB Store.empty atts).1 s = (run (committedReqs (execB Store.empty atts).2 s)).1 ∧
    deliveredAnswers (execB Store.empty atts).2 s = (run (committedReqs (execB Store.empty atts).2 s)).2 :=
  Service.cas_refines_run (S := coreService) atts s

/-- **An opening's id is fresh exactly when its stream has no event.** -/
theorem stream_id_new_iff_stream_empty {L : Log} (hv : Valid L) {c t : Id} {u : String} {m : Meta} :
    streamIdMustBeNew.holds (Past.view L t) (.streamOpened c t u m) = true ↔ onStream L t = [] := by
  simp only [streamIdMustBeNew, Past.view, Bool.not_eq_true']
  constructor
  · intro hm
    unfold onStream; rw [List.filter_eq_nil_iff]
    intro e he hs
    simp only [beq_iff_eq] at hs
    have := opened_of_mem hv he
    rw [hs, hm] at this; cases this
  · intro he
    cases hm : Past.opened L t
    · rfl
    · obtain ⟨e, hmem, hx⟩ := List.any_eq_true.mp hm
      have : e ∈ onStream L t := List.mem_filter.mpr ⟨hmem, by simp [opens_stream hx]⟩
      rw [he] at this; cases this

end Provenstream
