# Copyright 2026 the Provenstream authors. Licensed under the MIT License. See LICENSE.
# SPDX-License-Identifier: MIT
"""The negative proof tests: variants of the tasks layer (examples/tasks; a case naming `layer` and `lib` is a variant of
another layer), each an exact list of replacements applied to a copy of its sources. `run.py` builds each copy unchanged first (it must build), then the variant, which must fail to
build with its errors only where the case says.

Each case: `edits` (file, old text, new text: `old` must occur exactly once), `target` (the module built), and
`fails_in` (the declaration every error must lie in) and `fails_at` (a marker: some error must be on the line holding
it, when given).
"""

# A layer's own rules are what its theorems rest on: weaken one, and exactly the theorem drawn from it fails.

ANYONE_OPENS = {
    "name": "anyone-opens",
    "what": "the rule only_opener_can_open_tasks lets anyone open a task; the theorem that nobody creates work but the "
            "opener (tasks_opened_by_opener) must fail",
    "edits": [
        ("Tasks/Layer.lean",
         """               | .opened a .. => v.opener == some a | _ => true⟩,""",
         """               | .opened .. => true | _ => true⟩,"""),
    ],
    "target": "Tasks.Theorems",
    "fails_in": "tasks_opened_by_opener",
    "fails_at": None,
}

ANYONE_ASSIGNS = {
    "name": "anyone-assigns",
    "what": "the rule only_opener_can_assign lets anyone assign a task; the theorem that every assignee was named by the "
            "opener (assignees_named_by_opener) must fail",
    "edits": [
        ("Tasks/Layer.lean",
         """               | .assigned a .. => v.opener == some a | _ => true⟩,""",
         """               | .assigned .. => true | _ => true⟩,"""),
    ],
    "target": "Tasks.Theorems",
    "fails_in": "assignees_named_by_opener",
    "fails_at": None,
}

ANYONE_FINISHES = {
    "name": "anyone-finishes",
    "what": "the rule only_assignee_can_finish lets anyone complete a task; the theorem that a task is completed only "
            "by its assignee (completed_by_assignee) must fail",
    "edits": [
        ("Tasks/Layer.lean",
         """               | .completed a _ k _ => w.contains ("assigned", k, a) | _ => true⟩,""",
         """               | .completed .. => true | _ => true⟩,"""),
    ],
    "target": "Tasks.Theorems",
    "fails_in": "completed_by_assignee",
    "fails_at": None,
}

# A layer cannot loosen the core: a guard on a core command is tried after the core's rules, so it can only refuse more.

# The core's rules, unfolded, for `simp` to decide a core candidate against a concrete log.
CORE_SIMP = ("Provenstream.rejection, View.rejection, Provenstream.rules, streamIdMustBeNew, revisionUrlMustNameACommit, "
             "streamMustExist, streamMustBeOpen, onlyOpenerCanClose, Past.view, Past.opened, Past.closed, Past.opener, "
             "opens, closes, openerOf")

OTHER_CLOSES = {
    "name": "other-closes",
    "what": "a layer adds a guard meant to let someone other than the opener close a stream, and tries to prove a valid "
            "log where another principal closes; the attempt must fail at the step where the core refuses "
            "(only_opener_can_close), while the core's guarantee (every close is by the opener) builds in the same "
            "file",
    "edits": [
        ("Tasks/Layer.lean",
         """  memory := foldMemory [] addNotes notesToJ notesFromJ notesFromJ_toJ""",
         """  memory := foldMemory [] addNotes notesToJ notesFromJ notesFromJ_toJ
  guards := [⟨"anyone_may_close", ["stream.close"], fun _ _ _ => true⟩]"""),
        ("Tasks/Theorems.lean",
         """end Tasks
""",
         """/-- The core's guarantee, in this variant too: whoever closes is the opener. -/
theorem closer_is_opener {pre post : tasks.XLog} {g t : Id} {m : Meta}
    (h : ValidX (pre ++ .inl (Event.streamClosed g t m) :: post)) : Past.opener (cores pre) t = some g :=
  h.close_by_opener

/-- The attempt: a valid log in which someone other than the opener closes the stream. -/
theorem other_closes (a g t : Id) (u : String) (hu : validRevisionUrl u = true) (hne : g ≠ a) :
    ∃ log : tasks.XLog, ValidX log ∧ (.inl (Event.streamClosed g t none) : tasks.XEv) ∈ log := by
  have step1 : ValidX ([.inl (Event.streamOpened a t u none)] : tasks.XLog) :=
    (ValidX.snoc_inl_iff (L := tasks) (pre := []) (e := Event.streamOpened a t u none) .nil).mpr ⟨by
      simp [%(simp)s, hu], by simp⟩
  have step2 : ValidX ([.inl (Event.streamOpened a t u none), .inl (Event.streamClosed g t none)] : tasks.XLog) :=
    (ValidX.snoc_inl_iff (L := tasks) (pre := [.inl (Event.streamOpened a t u none)])
      (e := Event.streamClosed g t none) step1).mpr ⟨by -- MARK: the core refuses here
      simp [%(simp)s, hu, hne, Ne.symm hne], by simp⟩
  exact ⟨_, step2, by simp⟩

end Tasks
""" % {"simp": CORE_SIMP}),
    ],
    "target": "Tasks.Theorems",
    "fails_in": "other_closes",
    "fails_at": "MARK: the core refuses here",
}

CLOSE_TWICE = {
    "name": "close-twice",
    "what": "a layer adds a guard meant to accept a command the core refuses (a second close of a closed stream), and "
            "tries to prove a valid log where the opener closes twice; the attempt must fail at the step where the "
            "core refuses (stream_must_be_open), while the core's guarantee (nothing follows a close) builds in the "
            "same file",
    "edits": [
        ("Tasks/Layer.lean",
         """  memory := foldMemory [] addNotes notesToJ notesFromJ notesFromJ_toJ""",
         """  memory := foldMemory [] addNotes notesToJ notesFromJ notesFromJ_toJ
  guards := [⟨"closed_streams_may_close_again", ["stream.close"], fun _ _ _ => true⟩]"""),
        ("Tasks/Theorems.lean",
         """end Tasks
""",
         """/-- The core's guarantee, in this variant too: nothing follows a close. -/
theorem nothing_after_close {pre mid post : tasks.XLog} {a t : Id} {m : Meta} {x : tasks.XEv}
    (h : ValidX (pre ++ .inl (Event.streamClosed a t m) :: mid ++ x :: post)) : streamX x ≠ t :=
  h.close_final

/-- The attempt: a valid log in which the opener closes a stream twice. -/
theorem close_twice (a t : Id) (u : String) (hu : validRevisionUrl u = true) :
    ∃ log : tasks.XLog, ValidX log ∧ log.length = 3 := by
  have step1 : ValidX ([.inl (Event.streamOpened a t u none)] : tasks.XLog) :=
    (ValidX.snoc_inl_iff (L := tasks) (pre := []) (e := Event.streamOpened a t u none) .nil).mpr ⟨by
      simp [%(simp)s, hu], by simp⟩
  have step2 : ValidX ([.inl (Event.streamOpened a t u none), .inl (Event.streamClosed a t none)] : tasks.XLog) :=
    (ValidX.snoc_inl_iff (L := tasks) (pre := [.inl (Event.streamOpened a t u none)])
      (e := Event.streamClosed a t none) step1).mpr ⟨by
      simp [%(simp)s, hu], by simp⟩
  have step3 : ValidX ([.inl (Event.streamOpened a t u none), .inl (Event.streamClosed a t none),
      .inl (Event.streamClosed a t none)] : tasks.XLog) :=
    (ValidX.snoc_inl_iff (L := tasks) (pre := [.inl (Event.streamOpened a t u none), .inl (Event.streamClosed a t none)])
      (e := Event.streamClosed a t none) step2).mpr ⟨by -- MARK: the core refuses here
      simp [%(simp)s, hu], by simp⟩
  exact ⟨_, step3, rfl⟩

end Tasks
""" % {"simp": CORE_SIMP}),
    ],
    "target": "Tasks.Theorems",
    "fails_in": "close_twice",
    "fails_at": "MARK: the core refuses here",
}

TAKES_A_CORE_NAME = {
    "name": "takes-a-core-name",
    "what": "a layer names one of its commands stream.close, to answer the core's close with its own rules; the layer "
            "itself must fail to build (names_ok: a layer's command names are none of its base's)",
    "edits": [
        ("Tasks/Layer.lean",
         """{ name := "task.complete", event := "task.completed\"""",
         """{ name := "stream.close", event := "task.completed\""""),
        ("Tasks/Layer.lean",
         """    | .complete t k m => ("task.complete", [.s t, .s k, .m m])""",
         """    | .complete t k m => ("stream.close", [.s t, .s k, .m m])"""),
        ("Tasks/Layer.lean",
         """    | "task.complete", [.s t, .s k, .m m] => some (.complete t k m)""",
         """    | "stream.close", [.s t, .s k, .m m] => some (.complete t k m)"""),
    ],
    "target": "Tasks.Layer",
    "fails_in": "tasks",
    "fails_at": None,
}

# The work layer (examples/work): the same, for the rule its asks rest on.

ANYONE_ASKS = {
    "name": "anyone-asks",
    "what": "the work layer's rule only_assignee_can_ask lets anyone ask for a preparation; the theorem that only the "
            "assignee asks (asked_by_assignee) must fail",
    "layer": "examples/work",
    "lib": "Work",
    "edits": [
        ("Work/Layer.lean",
         """               | .asked a _ k _ _ => w.contains ("assigned", k, a) | _ => true⟩,""",
         """               | .asked .. => true | _ => true⟩,"""),
    ],
    "target": "Work.Theorems",
    "fails_in": "asked_by_assignee",
    "fails_at": None,
}

# The action layer (examples/action): the rule the gate rests on.

EVALUATOR_APPROVES_FORCED = {
    "name": "evaluator-approves-forced",
    "what": "the action layer's rule forced_needs_the_opener lets anyone approve a forced action; the theorem that only the "
            "opener approves one (only_the_opener_approves_a_forced_action) must fail",
    "layer": "examples/action",
    "lib": "Action",
    "edits": [
        ("Action/Layer.lean",
         """               | .approved a _ k _ => !noted w "forced" k || v.opener == some a | _ => true⟩,""",
         """               | .approved .. => true | _ => true⟩,"""),
    ],
    "target": "Action.Theorems",
    "fails_in": "only_the_opener_approves_a_forced_action",
    "fails_at": None,
}

CASES = [ANYONE_OPENS, ANYONE_ASSIGNS, ANYONE_FINISHES, OTHER_CLOSES, CLOSE_TWICE, TAKES_A_CORE_NAME, ANYONE_ASKS,
         EVALUATOR_APPROVES_FORCED]
