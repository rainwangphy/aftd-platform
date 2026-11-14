import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterCenteredBinomialGaussianSandwich

/-!
# energy_filter_floor_scaled_natAbs_limit

Topic: statistical_mechanics   Node: 97341f3daefc

Provenance: helper lemma. OP-892: centered binomial fourth-mass asymptotic via rescaled step functions and dominated convergence.

For every real x, the absolute value of floor(√k x), divided by √k, tends to |x|.
-/

theorem energy_filter_floor_scaled_natAbs_limit (x : ℝ) :
    Filter.Tendsto
      (fun k : ℕ => ((Int.floor (Real.sqrt (k:ℝ)*x)).natAbs : ℝ) / Real.sqrt (k:ℝ))
      Filter.atTop (nhds |x|) := by
  let z : ℕ → ℤ := fun k => Int.floor (Real.sqrt (k:ℝ)*x)
  have hroot : Filter.Tendsto (fun k : ℕ => Real.sqrt (k:ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Filter.Tendsto (fun k : ℕ => (Real.sqrt (k:ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hroot
  have hdist : ∀ᶠ k : ℕ in Filter.atTop,
      |(z k:ℝ)/Real.sqrt (k:ℝ)-x| ≤ (Real.sqrt (k:ℝ))⁻¹ := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hp : 0 < Real.sqrt (k:ℝ) := by positivity
    have hfloor := Int.floor_le (Real.sqrt (k:ℝ)*x)
    have hceil := Int.lt_floor_add_one (Real.sqrt (k:ℝ)*x)
    have hab : |(z k:ℝ)-Real.sqrt (k:ℝ)*x| ≤ 1 := by
      apply abs_le.mpr
      dsimp [z] at *
      constructor <;> linarith
    have heq : (z k:ℝ)/Real.sqrt (k:ℝ)-x =
        ((z k:ℝ)-Real.sqrt (k:ℝ)*x)/Real.sqrt (k:ℝ) := by field_simp
    rw [heq, abs_div, abs_of_pos hp]
    rw [← one_div]
    exact (div_le_div_iff_of_pos_right hp).2 hab
  have habs : Filter.Tendsto (fun k : ℕ => |(z k:ℝ)/Real.sqrt (k:ℝ)-x|) Filter.atTop (nhds 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun k => abs_nonneg _) hdist hinv
  have hz : Filter.Tendsto (fun k : ℕ => (z k:ℝ)/Real.sqrt (k:ℝ)) Filter.atTop (nhds x) := by
    apply tendsto_sub_nhds_zero_iff.mp
    exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs
  have hzabs := hz.abs
  convert hzabs using 1
  funext k
  have hcast : ((z k).natAbs : ℝ) = |(z k:ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [hcast, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
