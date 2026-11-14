import AFTD.Prelude

/-!
# energy_filter_floor_distance_le_one

Topic: statistical_mechanics   Node: bbb6c880dc16

Provenance: helper lemma. OP-892: centered binomial fourth-mass asymptotic via rescaled step functions and dominated convergence.

If h≥1 then for every real x the distance between x and floor(hx)/h is at most one.
-/

theorem energy_filter_floor_distance_le_one (h x : ℝ) (hh : 1 ≤ h) :
    |x - (Int.floor (h*x):ℝ)/h| ≤ 1 := by
  have hp : 0 < h := by linarith
  have hf := Int.floor_le (h*x)
  have hc := Int.lt_floor_add_one (h*x)
  have hab : |(Int.floor (h*x):ℝ)-h*x| ≤ 1 := by
    apply abs_le.mpr
    constructor <;> linarith
  have heq : x - (Int.floor (h*x):ℝ)/h =
      -(((Int.floor (h*x):ℝ)-h*x)/h) := by field_simp; ring
  rw [heq, abs_neg, abs_div, abs_of_pos hp]
  calc
    _ ≤ 1 / h := (div_le_div_iff_of_pos_right hp).2 hab
    _ ≤ 1 := (div_le_one hp).2 hh
