import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterFloorScaledNatAbsLimit

/-!
# energy_filter_floor_offset_scaled_natAbs_limit

Topic: statistical_mechanics   Node: cbda4b81552a

Provenance: helper lemma. OP-892: direct shifted-binomial kernel limit and uniform bound.

For real x and integer h, the absolute value of floor(√k x)+h divided by √k tends to |x|.
-/

theorem energy_filter_floor_offset_scaled_natAbs_limit (x : ℝ) (h : ℤ) :
    Filter.Tendsto
      (fun k : ℕ => ((Int.floor (Real.sqrt (k:ℝ)*x)+h).natAbs : ℝ) / Real.sqrt (k:ℝ))
      Filter.atTop (nhds |x|) := by
  let z : ℕ → ℤ := fun k => Int.floor (Real.sqrt (k:ℝ)*x)
  let A : ℕ → ℝ := fun k => ((z k+h).natAbs : ℝ)/Real.sqrt (k:ℝ)
  let B : ℕ → ℝ := fun k => ((z k).natAbs : ℝ)/Real.sqrt (k:ℝ)
  have hB : Filter.Tendsto B Filter.atTop (nhds |x|) := energy_filter_floor_scaled_natAbs_limit x
  have hroot : Filter.Tendsto (fun k : ℕ => Real.sqrt (k:ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Filter.Tendsto (fun k : ℕ => (Real.sqrt (k:ℝ))⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hroot
  have hbnd : ∀ᶠ k : ℕ in Filter.atTop, |A k-B k| ≤ |(h:ℝ)| * (Real.sqrt (k:ℝ))⁻¹ := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hp : 0 < Real.sqrt (k:ℝ) := by positivity
    have hdiff : abs (abs ((z k:ℝ)+(h:ℝ)) - abs (z k:ℝ)) ≤ |(h:ℝ)| := by
      have ht := abs_abs_sub_abs_le_abs_sub ((z k:ℝ)+(h:ℝ)) (z k:ℝ)
      simpa using ht
    dsimp [A,B]
    rw [Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs, Int.cast_add]
    rw [← sub_div, abs_div, abs_of_pos hp, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hdiff (inv_nonneg.mpr hp.le)
  have hzero : Filter.Tendsto (fun k => |A k-B k|) Filter.atTop (nhds 0) := by
    have ht : Filter.Tendsto (fun k : ℕ => |(h:ℝ)| * (Real.sqrt (k:ℝ))⁻¹)
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := |(h:ℝ)|)).mul hinv
    exact squeeze_zero' (Filter.Eventually.of_forall fun k => abs_nonneg _) hbnd ht
  have hdiff : Filter.Tendsto (fun k => A k-B k) Filter.atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr hzero
  have ht := hdiff.add hB
  simp only [zero_add] at ht
  convert ht using 1
  funext k
  dsimp [A,B,z]
  ring
