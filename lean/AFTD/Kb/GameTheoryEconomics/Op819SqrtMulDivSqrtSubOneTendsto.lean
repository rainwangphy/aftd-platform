import AFTD.Prelude

/-!
# op819_sqrt_mul_div_sqrt_sub_one_tendsto

Topic: fair_division   Node: cdf7fa62341a

Provenance: helper lemma. step towards op819_online_single_high_efx_sharp_sqrt_law

The sequence sqrt(R) * (sqrt(R) - 1)⁻¹ converges to 1 as R tends to infinity.
-/

/-- The sequence sqrt(R) * (sqrt(R) - 1)⁻¹ converges to 1 as R tends to infinity. -/
theorem op819_sqrt_mul_div_sqrt_sub_one_tendsto :
    Filter.Tendsto (fun R : ℕ => Real.sqrt (R : ℝ) * (Real.sqrt (R : ℝ) - 1)⁻¹) Filter.atTop (nhds 1) := by
  have h1 : Filter.Tendsto (fun R : ℕ => Real.sqrt (R : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h2 : Filter.Tendsto (fun R : ℕ => Real.sqrt (R : ℝ) - 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ) h1
  have h3 : Filter.Tendsto (fun R : ℕ => (Real.sqrt (R : ℝ) - 1)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp h2
  have h4 : Filter.Tendsto (fun R : ℕ => 1 + (Real.sqrt (R : ℝ) - 1)⁻¹) Filter.atTop (nhds 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add h3
    rw [add_zero] at h
    exact h
  have heq : (fun R : ℕ => 1 + (Real.sqrt (R : ℝ) - 1)⁻¹) =ᶠ[Filter.atTop]
      (fun R : ℕ => Real.sqrt (R : ℝ) * (Real.sqrt (R : ℝ) - 1)⁻¹) := by
    rw [Filter.EventuallyEq, Filter.eventually_atTop]
    use 2
    intro R hR
    have hne : Real.sqrt (R : ℝ) - 1 ≠ 0 := by
      intro h
      have h_sqrt : Real.sqrt (R : ℝ) = 1 := sub_eq_zero.mp h
      rw [Real.sqrt_eq_one] at h_sqrt
      have : (R : ℝ) ≥ 2 := by exact_mod_cast hR
      linarith
    symm
    calc
      Real.sqrt (R : ℝ) * (Real.sqrt (R : ℝ) - 1)⁻¹
        = (Real.sqrt (R : ℝ) - 1 + 1) * (Real.sqrt (R : ℝ) - 1)⁻¹ := by rw [sub_add_cancel]
      _ = (Real.sqrt (R : ℝ) - 1) * (Real.sqrt (R : ℝ) - 1)⁻¹ + 1 * (Real.sqrt (R : ℝ) - 1)⁻¹ := by rw [add_mul]
      _ = 1 + (Real.sqrt (R : ℝ) - 1)⁻¹ := by rw [mul_inv_cancel₀ hne, one_mul]
  exact h4.congr' heq
