import AFTD.Prelude
import AFTD.Kb.NumberTheory.ArithmeticFourierBound

/-!
# arithmetic_fourier_bound_three

Topic: elementary_number_theory   Node: e1ba42f52e70

Provenance: helper lemma. step towards op716_fourier_threshold_odd_eq_arithmetic_bound

The arithmetic Fourier bound lambda_3 in dimension 3 equals 5.
-/

/-- The arithmetic Fourier bound lambda_3 in dimension 3 equals 5. -/
theorem arithmetic_fourier_bound_three : arithmetic_fourier_bound 3 = 5 := by
  unfold arithmetic_fourier_bound
  have h5 : 5 ∈ {n : ℕ | n % 3 = 2 ∧ 8 * (2 ^ 3 - 1) + 2 * n + (if n % 2 = 1 then 9 else 0) ≤ 3 * n ^ 2} := by
    decide
  apply le_antisymm
  · exact Nat.sInf_le h5
  · apply le_csInf
    · exact ⟨5, h5⟩
    · intro b hb
      dsimp at hb
      rcases hb with ⟨hb1, hb2⟩
      by_contra! h
      interval_cases b <;> revert hb1 hb2 <;> decide
