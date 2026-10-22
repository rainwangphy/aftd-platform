import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicShift
import AFTD.Kb.Tcs.IsCyclicCode

/-!
# is_cyclic_code_bot

Topic: information   Node: 364f3d4c6da3

Provenance: helper lemma. arXiv:2610.28047 Section 2.3

The zero subspace of Fin n → F is a cyclic code.
-/

/-- The zero code is cyclic. -/
theorem is_cyclic_code_bot {F : Type*} [Field F] (n : ℕ) : is_cyclic_code n (⊥ : Subspace F (Fin n → F)) := by
  intro v hv
  rw [Submodule.mem_bot] at hv
  rw [Submodule.mem_bot]
  subst hv
  unfold cyclic_shift
  split_ifs with hn <;> rfl
