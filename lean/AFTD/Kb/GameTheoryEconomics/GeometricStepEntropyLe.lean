import AFTD.Prelude

/-!
# geometric_step_entropy_le

Topic: social_choice   Node: 007b7e787996

For a finite set K of exponents containing 0 and 0 < phi < 1, the entropy of the distribution proportional to phi^k on K is at most log(1/(1-phi)) + log(1/phi) * phi/(1-phi)^2.
-/

/-- One step of the process: the entropy of the normalised weights `φ^k / Z` over a finite set `K ∋ 0` of exponents is at most `log (1/(1-φ)) + (-log φ) * φ/(1-φ)^2`. -/
lemma geometric_step_entropy_le (φ : ℝ) (h0 : 0 < φ) (h1 : φ < 1) (K : Finset ℕ) (hK : 0 ∈ K) :
    ∑ k ∈ K, Real.negMulLog (φ ^ k / ∑ j ∈ K, φ ^ j) ≤
      Real.log (1 - φ)⁻¹ + (-Real.log φ) * (φ / (1 - φ) ^ 2) := by
  set Z := ∑ j ∈ K, φ ^ j with hZ
  have hnorm : ‖φ‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos h0]; exact h1
  have hZ1 : 1 ≤ Z := by
    have := Finset.single_le_sum (f := fun j => φ ^ j) (fun j _ => (pow_pos h0 j).le) hK
    simpa using this
  have hZpos : 0 < Z := by linarith
  have hZle : Z ≤ (1 - φ)⁻¹ := by
    rw [← tsum_geometric_of_lt_one h0.le h1]
    exact (summable_geometric_of_lt_one h0.le h1).sum_le_tsum K (fun j _ => (pow_pos h0 j).le)
  have hS : ∑ k ∈ K, (k : ℝ) * φ ^ k ≤ φ / (1 - φ) ^ 2 := by
    rw [← tsum_coe_mul_geometric_of_norm_lt_one hnorm]
    exact (summable_pow_mul_geometric_of_norm_lt_one 1 hnorm |>.congr fun j => by simp).sum_le_tsum K
      (fun j _ => mul_nonneg (Nat.cast_nonneg j) (pow_pos h0 j).le)
  have hlogφ : 0 ≤ -Real.log φ := by linarith [Real.log_neg h0 h1]
  have key : ∀ k ∈ K, Real.negMulLog (φ ^ k / Z) =
      φ ^ k / Z * Real.log Z + (-Real.log φ) * ((k : ℝ) * φ ^ k) / Z := by
    intro k _
    rw [Real.negMulLog, Real.log_div (pow_pos h0 k).ne' hZpos.ne', Real.log_pow]
    field_simp
    ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div,
    div_self hZpos.ne', one_mul, ← Finset.sum_div, ← Finset.mul_sum]
  refine add_le_add (Real.log_le_log hZpos hZle) ?_
  calc (-Real.log φ) * (∑ k ∈ K, (k : ℝ) * φ ^ k) / Z
      ≤ (-Real.log φ) * ∑ k ∈ K, (k : ℝ) * φ ^ k :=
        div_le_self (mul_nonneg hlogφ (Finset.sum_nonneg fun j _ =>
          mul_nonneg (Nat.cast_nonneg j) (pow_pos h0 j).le)) hZ1
    _ ≤ (-Real.log φ) * (φ / (1 - φ) ^ 2) := mul_le_mul_of_nonneg_left hS hlogφ
