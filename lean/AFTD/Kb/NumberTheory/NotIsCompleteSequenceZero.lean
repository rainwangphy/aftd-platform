import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsCompleteSequence

/-!
# not_is_complete_sequence_zero

Topic: elementary_number_theory   Node: 539926b6acdd

Provenance: helper lemma. folklore

The constant zero sequence is not a complete sequence.
-/

/-- The constant zero sequence is not a complete sequence. -/
theorem not_is_complete_sequence_zero :
    ¬ is_complete_sequence (fun _ => 0) := by
  intro h
  obtain ⟨S, -, hsum⟩ := h 1 (by decide)
  simp at hsum
