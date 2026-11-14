import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterFloorOffsetScaledNatAbsLimit
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialRescaledPointwise
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeightEqNatAbs
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialWeight

/-!
# energy_filter_floor_offset_weight_pointwise

Topic: statistical_mechanics   Node: 64fc8c8262b0

Provenance: helper lemma. OP-892: direct shifted-binomial kernel limit and uniform bound.

For real x and fixed integer h, the centered binomial weight at floor(√k x)+h tends to exp(−x²).
-/

theorem energy_filter_floor_offset_weight_pointwise (x : ℝ) (h : ℤ) :
    Filter.Tendsto (fun k : ℕ => energy_filter_centered_binomial_weight k
      (Int.floor (Real.sqrt (k:ℝ)*x)+h)) Filter.atTop (nhds (Real.exp (-x^2))) := by
  let j : ℕ → ℕ := fun k => (Int.floor (Real.sqrt (k:ℝ)*x)+h).natAbs
  have hscale : Filter.Tendsto (fun k : ℕ => (j k:ℝ)/Real.sqrt (k:ℝ)) Filter.atTop (nhds |x|) :=
    energy_filter_floor_offset_scaled_natAbs_limit x h
  have hroot : Filter.Tendsto (fun k : ℕ => Real.sqrt (k:ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Filter.Tendsto (fun k : ℕ => (Real.sqrt (k:ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hroot
  have hjk : Filter.Tendsto (fun k : ℕ => (j k:ℝ)/(k:ℝ)) Filter.atTop (nhds 0) := by
    have hh := hscale.mul hinv
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hp : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hs : Real.sqrt (k:ℝ) ≠ 0 := by positivity
    have he : Real.sqrt (k:ℝ)^2 = (k:ℝ) := Real.sq_sqrt (le_of_lt hp)
    field_simp
    nlinarith [he]
  have hvalid : ∀ᶠ k : ℕ in Filter.atTop, j k ≤ k := by
    have hsmall : ∀ᶠ k : ℕ in Filter.atTop, (j k:ℝ)/(k:ℝ) < 1 :=
      hjk.eventually (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num))
    filter_upwards [hsmall, Filter.eventually_ge_atTop 1] with k hj hk
    have hp : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hj' : (j k:ℝ) < k := (div_lt_one hp).mp hj
    exact le_of_lt (by exact_mod_cast hj')
  have ht := energy_filter_centered_binomial_rescaled_pointwise j |x| hscale hvalid
  have he : Real.exp (-|x|^2) = Real.exp (-x^2) := by rw [sq_abs]
  rw [he] at ht
  apply ht.congr'
  filter_upwards [hvalid] with k hk
  exact (energy_filter_centered_binomial_weight_eq_natAbs k _ hk).symm
