import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterNonnegativeFourthPowerConvolutionControl

/-!
# energy_filter_abs_convolution_control

Topic: statistical_mechanics   Node: 1bb95f3ac37c

Provenance: helper lemma. OP-892: convolution and quartic-cycle summability.

For a real integer sequence a in ℓ^(4/3), each absolute convolution sum is finite and the squares of those sums form a summable sequence.
-/

theorem energy_filter_abs_convolution_control
    (a : ℤ → ℝ) (ha_lp : Memℓp a (4 / 3)) :
    (∀ m : ℤ, Summable (fun j : ℤ => |a j * a (m-j)|)) ∧
    Summable (fun m : ℤ => (∑' j : ℤ, |a j * a (m-j)|)^2) := by
  let u : ℤ → ℝ := fun i => |a i| ^ (1/3:ℝ)
  have hu0 (i : ℤ) : 0 ≤ u i := Real.rpow_nonneg (abs_nonneg _) _
  have hu3 (i : ℤ) : u i ^ 3 = |a i| := by
    dsimp [u]
    rw [← Real.rpow_mul_natCast (abs_nonneg _) (1/3:ℝ) 3]
    norm_num
  have hu4 (i : ℤ) : u i ^ 4 = |a i| ^ (4/3:ℝ) := by
    dsimp [u]
    rw [← Real.rpow_mul_natCast (abs_nonneg _) (1/3:ℝ) 4]
    norm_num
  have hp : 0 < ((4/3:ENNReal)).toReal := by norm_num
  have hnorm := ha_lp.summable hp
  have hu : Summable (fun i => u i ^ 4) := by
    convert hnorm using 1
    funext i
    rw [hu4, Real.norm_eq_abs]
    norm_num
  obtain ⟨hconv, hconv2⟩ := energy_filter_nonnegative_fourth_power_convolution_control u hu0 hu
  have hconv_abs (m : ℤ) : Summable (fun j : ℤ => |a j * a (m-j)|) := by
    convert hconv m using 1
    funext j
    rw [hu3, hu3, abs_mul]
  have hconv2' : Summable (fun m : ℤ => (∑' j : ℤ, |a j * a (m-j)|)^2) := by
    convert hconv2 using 1
    funext m
    congr 1
    apply tsum_congr
    intro j
    rw [hu3, hu3, abs_mul]
  exact ⟨hconv_abs, hconv2'⟩
