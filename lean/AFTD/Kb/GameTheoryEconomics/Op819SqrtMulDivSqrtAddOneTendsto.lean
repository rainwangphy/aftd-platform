import AFTD.Prelude

/-!
# op819_sqrt_mul_div_sqrt_add_one_tendsto

Topic: fair_division   Node: 8877fcc6b7fa

Provenance: helper lemma. step towards op819_online_single_high_efx_sharp_sqrt_law

The sequence sqrt(R) * (sqrt(R) + 1)⁻¹ converges to 1 as R tends to infinity.
-/

/-- The sequence sqrt(R) * (sqrt(R) + 1)⁻¹ converges to 1 as R tends to infinity. -/
theorem op819_sqrt_mul_div_sqrt_add_one_tendsto :
    Filter.Tendsto (fun R : ℕ => Real.sqrt (R : ℝ) * (Real.sqrt (R : ℝ) + 1)⁻¹) Filter.atTop (nhds 1) := by
  have hsqrt : Filter.Tendsto (fun R : ℕ => Real.sqrt (R : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hden : Filter.Tendsto (fun R : ℕ => Real.sqrt (R : ℝ) + 1) Filter.atTop Filter.atTop :=
    hsqrt.atTop_add tendsto_const_nhds
  have hinv : Filter.Tendsto (fun R : ℕ => (Real.sqrt (R : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) :=
    hden.inv_tendsto_atTop
  have hsub : Filter.Tendsto (fun R : ℕ => (1 : ℝ) - (Real.sqrt (R : ℝ) + 1)⁻¹)
      Filter.atTop (nhds (1 - 0)) :=
    tendsto_const_nhds.sub hinv
  have hEq : (fun R : ℕ => Real.sqrt (R : ℝ) * (Real.sqrt (R : ℝ) + 1)⁻¹)
      = (fun R : ℕ => (1 : ℝ) - (Real.sqrt (R : ℝ) + 1)⁻¹) := by
    funext R
    rw [eq_sub_iff_add_eq]
    field_simp
  rw [hEq]
  simpa using hsub
