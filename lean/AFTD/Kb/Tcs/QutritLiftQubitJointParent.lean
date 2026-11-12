import AFTD.Prelude

/-!
# qutrit_lift_qubit_joint_parent

Topic: quantum   Node: 87039674861d

Provenance: helper lemma. Local compatibility helper for OP-693.

A joint qubit parent lifts by a linear map to a positive qutrit parent on its range.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem qutrit_lift_qubit_joint_parent
    (M : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ) (U : Matrix (Fin 3) (Fin 2) ℂ)
    (G : (Fin 3 → Bool) → Matrix (Fin 2) (Fin 2) ℂ)
    (hG : ∀ s, (G s).PosSemidef) (hsum : (∑ s, G s) = 1)
    (hmarg : ∀ j, (∑ s, if s j then G s else 0) = Uᴴ * M j * U) :
    ∃ H : (Fin 3 → Bool) → Matrix (Fin 3) (Fin 3) ℂ,
      (∀ s, (H s).PosSemidef) ∧ (∑ s, H s) = U*Uᴴ ∧
      ∀ j : Fin 3, (∑ s, if s j then H s else 0) = (U*Uᴴ)*M j*(U*Uᴴ) := by
  let lift (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 3) (Fin 3) ℂ := U * X * Uᴴ
  have hzero : lift 0 = 0 := by
    ext i j
    simp [lift, Matrix.mul_apply]
  have hlin (f : (Fin 3 → Bool) → Matrix (Fin 2) (Fin 2) ℂ) :
      (∑ s, lift (f s)) = lift (∑ s, f s) := by
    ext i j
    simp only [Matrix.sum_apply]
    simp [lift, Matrix.mul_apply, Matrix.sum_apply, Fin.sum_univ_two,
      Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm, add_mul]
  refine ⟨fun s => lift (G s), ?_, ?_, ?_⟩
  · intro s
    exact (hG s).mul_mul_conjTranspose_same U
  · rw [hlin, hsum]
    simp [lift]
  · intro j
    have heq : (∑ s, if s j then lift (G s) else 0) =
        ∑ s, lift (if s j then G s else 0) := by
      apply Finset.sum_congr rfl
      intro s hs
      cases h : s j <;> simp [h, hzero]
    rw [heq, hlin, hmarg]
    dsimp [lift]
    rw [← Matrix.mul_assoc U (Uᴴ * M j) U, ← Matrix.mul_assoc U Uᴴ (M j)]
    exact Matrix.mul_assoc _ _ _
