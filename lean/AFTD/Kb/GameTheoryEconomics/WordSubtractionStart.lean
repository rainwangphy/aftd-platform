import AFTD.Prelude

/-!
# word_subtraction_start

Topic: combinatorial_games   Node: d2f5cf3f8835

Provenance: helper lemma. step towards word_subtraction_is_regular

The start state of the automaton: an empty buffer and status bits that are true exactly for indices j ≥ 1 (which are vacuously correct at the empty word).
-/

/-- Start state: empty buffer, all status bits true except bit 0. -/
noncomputable def word_subtraction_start {α : Type*} (n : ℕ) : (Fin n → Option α) × (Fin (n + 1) → Bool) := (fun _ => none, fun j => decide (0 < (j : ℕ)))
