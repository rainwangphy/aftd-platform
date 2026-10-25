import AFTD.Prelude
import AFTD.Kb.Tcs.HasFractionalScdWithDenominator
import AFTD.Kb.Tcs.IsSymmetricSaturatedChain

/-!
# fractional_scd_with_denominator_mul

Topic: combinatorics   Node: 394379bde958

Provenance: helper lemma. arXiv:2610.24148, Section 2.7.4

If a partially ordered type with an integer rank function admits a fractional symmetric chain decomposition with denominator D, then for every positive integer m it also admits a fractional symmetric chain decomposition with denominator D * m.
-/

open scoped Classical BigOperators in
/-- A fractional SCD with denominator D also has denominator D * m for any positive integer m. -/
theorem fractional_scd_with_denominator_mul
    {α : Type*} [PartialOrder α] (rank : α → ℤ) (D m : ℕ) (hm : 0 < m)
    (h : has_fractional_scd_with_denominator rank D) :
    has_fractional_scd_with_denominator rank (D * m) := by
  rcases h with ⟨𝒞, τ, h_symm, h_pos, h_den, h_sum⟩
  refine ⟨𝒞, τ, h_symm, h_pos, ?_, h_sum⟩
  intro C hC
  rcases h_den C hC with ⟨k, hk⟩
  refine ⟨k * m, ?_⟩
  rw [hk]
  push_cast
  have hm_ne : (m : ℚ) ≠ 0 := by positivity
  exact (mul_div_mul_right (k : ℚ) (D : ℚ) hm_ne).symm
