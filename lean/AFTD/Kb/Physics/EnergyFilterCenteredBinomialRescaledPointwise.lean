import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialGaussianSandwich

/-!
# energy_filter_centered_binomial_rescaled_pointwise

Topic: statistical_mechanics   Node: d2113bbbcb1e

Provenance: helper lemma. OP-892: centered binomial fourth-mass asymptotic via rescaled step functions and dominated convergence.

If j(k)≤k eventually and j(k)/√k tends to x, then choose(2k,k+j(k))/choose(2k,k) tends to exp(−x²).
-/

theorem energy_filter_centered_binomial_rescaled_pointwise
    (j : ℕ → ℕ) (x : ℝ)
    (hscale : Filter.Tendsto (fun k : ℕ => (j k : ℝ) / Real.sqrt (k : ℝ)) Filter.atTop (nhds x))
    (hvalid : ∀ᶠ k : ℕ in Filter.atTop, j k ≤ k) :
    Filter.Tendsto (fun k : ℕ =>
      (Nat.choose (2*k) (k+j k) : ℝ) / (Nat.choose (2*k) k : ℝ))
      Filter.atTop (nhds (Real.exp (-x^2))) := by
  have hroot : Filter.Tendsto (fun k : ℕ => Real.sqrt (k:ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Filter.Tendsto (fun k : ℕ => (Real.sqrt (k:ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hroot
  have hjk : Filter.Tendsto (fun k : ℕ => (j k : ℝ)/(k:ℝ)) Filter.atTop (nhds 0) := by
    have hh := hscale.mul hinv
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hkreal : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hsqrt : Real.sqrt (k:ℝ) ≠ 0 := by positivity
    have hsquare : Real.sqrt (k:ℝ)^2 = (k:ℝ) := Real.sq_sqrt (le_of_lt hkreal)
    field_simp
    nlinarith [hsquare]
  have hsq : Filter.Tendsto (fun k : ℕ => (j k : ℝ)^2/(k:ℝ)) Filter.atTop (nhds (x^2)) := by
    have hh := hscale.pow 2
    apply hh.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hkreal : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hsqrt : Real.sqrt (k:ℝ) ≠ 0 := by positivity
    have hsquare : Real.sqrt (k:ℝ)^2 = (k:ℝ) := Real.sq_sqrt (le_of_lt hkreal)
    field_simp
    nlinarith [hsquare]
  have hinvk : Filter.Tendsto (fun k : ℕ => (1:ℝ)/(k:ℝ)) Filter.atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hu : Filter.Tendsto (fun k : ℕ => (j k : ℝ)^2 / ((k:ℝ)+(j k:ℝ)))
      Filter.atTop (nhds (x^2)) := by
    have hd : Filter.Tendsto (fun k : ℕ => 1 + (j k:ℝ)/(k:ℝ)) Filter.atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add hjk
    have hh := hsq.div hd (one_ne_zero : (1:ℝ) ≠ 0)
    simp only [div_one] at hh
    apply hh.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hkreal : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hkp : (0:ℝ) < (k:ℝ)+(j k:ℝ) := by positivity
    simp only [Pi.div_apply]
    field_simp
  have hl : Filter.Tendsto (fun k : ℕ => (j k : ℝ)^2 / ((k:ℝ)-(j k:ℝ)+1))
      Filter.atTop (nhds (x^2)) := by
    have hd : Filter.Tendsto (fun k : ℕ => 1 - (j k:ℝ)/(k:ℝ) + (1:ℝ)/(k:ℝ)) Filter.atTop (nhds 1) := by
      simpa using (tendsto_const_nhds.sub hjk).add hinvk
    have hh := hsq.div hd (one_ne_zero : (1:ℝ) ≠ 0)
    simp only [div_one] at hh
    apply hh.congr'
    filter_upwards [Filter.eventually_ge_atTop 1, hvalid] with k hk hj
    have hkreal : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hjr : (j k:ℝ) ≤ k := by exact_mod_cast hj
    have hkp : (0:ℝ) < (k:ℝ)-(j k:ℝ)+1 := by linarith
    simp only [Pi.div_apply]
    field_simp
  have hlu := (Real.continuous_exp.tendsto (-x^2)).comp hl.neg
  have huu := (Real.continuous_exp.tendsto (-x^2)).comp hu.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlu huu
  · filter_upwards [Filter.eventually_ge_atTop 1, hvalid] with k hk hj
    exact (energy_filter_centered_binomial_gaussian_sandwich k (j k) hk hj).1
  · filter_upwards [Filter.eventually_ge_atTop 1, hvalid] with k hk hj
    exact (energy_filter_centered_binomial_gaussian_sandwich k (j k) hk hj).2
