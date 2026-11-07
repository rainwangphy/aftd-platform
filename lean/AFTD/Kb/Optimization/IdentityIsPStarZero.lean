import AFTD.Prelude
import AFTD.Kb.Optimization.IsPStarKappa

/-!
# identity_is_p_star_zero

Topic: lp_duality   Node: df681e0d8bbd

Provenance: helper lemma. arXiv:2611.07815 Section 1

For every dimension n, the n-by-n real identity matrix belongs to P*(0).
-/

/-- The identity matrix belongs to P*(0). -/
theorem identity_is_p_star_zero (n : ℕ) : is_p_star_kappa n 1 0 := by
  constructor
  · norm_num
  · intro x
    simp only [Matrix.one_mulVec, mul_zero, add_zero, one_mul]
    have hneg : ∑ i : Fin n with x i * x i < 0, x i * x i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have h := (Finset.mem_filter.mp hi).2
      have h' := mul_self_nonneg (x i)
      linarith
    have hpos : 0 ≤ ∑ i : Fin n with 0 < x i * x i, x i * x i :=
      Finset.sum_nonneg (fun i hi => le_of_lt (Finset.mem_filter.mp hi).2)
    linarith
