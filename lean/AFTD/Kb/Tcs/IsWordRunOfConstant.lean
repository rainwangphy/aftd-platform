import AFTD.Prelude
import AFTD.Kb.Tcs.IsWordRun
import AFTD.Kb.Tcs.IsConstantWord

/-!
# is_word_run_of_constant

Topic: information   Node: 8399bc34a6f4

Provenance: helper lemma. folklore

For any constant word y on Fin n with 1 ≤ n, the full interval [0, n) is a run of y.
-/

/-- For any constant word on Fin n with 1 ≤ n, the full interval [0, n) is a run. -/
theorem is_word_run_of_constant {n : ℕ} {α : Type*} (y : Fin n → α)
    (hconst : is_constant_word y) (hn : 1 ≤ n) : is_word_run y 0 n := by
  refine ⟨hn, le_rfl, ?_, Or.inl rfl, Or.inl rfl⟩
  intro i hi
  exact hconst i ⟨0, hn⟩
