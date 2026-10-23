import AFTD.Prelude
import AFTD.Kb.Tcs.LinearFlatteningTestableZeroOrder
import AFTD.Kb.Tcs.LinearFlatteningTestable
import AFTD.Kb.Tcs.LinearFlatteningPotencyGt
import AFTD.Kb.Tcs.Tensor3Pure

/-!
# linear_flattening_testable_one_iff_zero

Topic: algebraic_complexity   Node: 1b2768d55959

Provenance: helper lemma. step towards linear_flattening_testable_even_step

At dimension n = 1 the secant variety σ_r((ℂ¹)⊗³) is testable by the linear flattening method if and only if r = 0, i.e. the supremum of the potency over all linear flattenings on (ℂ¹)⊗³ is exactly 1.
-/

/-- Exact small instance: at dimension 1 every linear flattening has potency at most 1, so the only testable order is 0. -/
theorem linear_flattening_testable_one_iff_zero (r : ℕ) :
    linear_flattening_testable 1 r ↔ r = 0 := by
  constructor
  · intro h
    rcases h with ⟨u, v, L, T, hT⟩
    by_contra hr
    have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr
    have hT_spec : r * (L (tensor3_pure 1 1 1)).rank < (L T).rank := hT 1 1 1
    have hLT : L T = (T 0 0 0) • L (tensor3_pure 1 1 1) := by
      have hT_eq : T = (T 0 0 0) • tensor3_pure 1 1 1 := by
        ext i j k
        simp [tensor3_pure, Subsingleton.elim i 0, Subsingleton.elim j 0, Subsingleton.elim k 0]
      conv_lhs => rw [hT_eq]
      rw [map_smul]
    have h_rank_le : (L T).rank ≤ (L (tensor3_pure 1 1 1)).rank := by
      rw [hLT]
      by_cases hc : T 0 0 0 = 0
      · rw [hc, zero_smul, Matrix.rank_zero]
        exact Nat.zero_le _
      · have h_mem : T 0 0 0 ∈ nonZeroDivisors ℂ := mem_nonZeroDivisors_of_ne_zero hc
        rw [Matrix.rank_smul_of_mem_nonZeroDivisors (L (tensor3_pure 1 1 1)) h_mem]
    have h_le : (L (tensor3_pure 1 1 1)).rank ≤ r * (L (tensor3_pure 1 1 1)).rank := by
      calc (L (tensor3_pure 1 1 1)).rank = 1 * (L (tensor3_pure 1 1 1)).rank := by rw [one_mul]
      _ ≤ r * (L (tensor3_pure 1 1 1)).rank := Nat.mul_le_mul_right (L (tensor3_pure 1 1 1)).rank hr1
    omega
  · rintro rfl
    exact linear_flattening_testable_zero_order 1 le_rfl
