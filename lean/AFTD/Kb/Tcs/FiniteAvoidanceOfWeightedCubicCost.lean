import AFTD.Prelude

/-!
# finite_avoidance_of_weighted_cubic_cost

Topic: graphs   Node: d6234d1ebf77

Provenance: helper lemma. IN-342 resumed helper for OP-306, arXiv:2610.22142 Sections3.3.2 and6. This is a weighted interface to the existing finite/adaptive cubic avoidance route. The new proposed square-polynomial weighting of invalid-color counts is tested only in experiments8807,8812,8822,8824. No uniform inequality, novel wild-number bound, or research advance is asserted by this conditional helper.

For any natural-valued defect function on a finite sample space and any nonnegative real weights, a strictly negative weighted sum of (d-1)(d-3)(d-4) guarantees a sample with zero defects. This is elementary weighted finite averaging, not a uniform moment bound.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem finite_avoidance_of_weighted_cubic_cost
    {J : Type*} [Fintype J] (d : J → ℕ) (w : J → ℝ)
    (hw : ∀ j,0≤w j)
    (h : (∑ j,w j*((d j : ℝ)-1)*((d j : ℝ)-3)*((d j : ℝ)-4))<0) :
    ∃ j,d j=0 := by
  by_contra! hno
  have hp (j : J) : 0≤((d j : ℝ)-1)*((d j : ℝ)-3)*((d j : ℝ)-4) := by
    have hd : (1 : ℝ)≤d j := by exact_mod_cast (show 1≤d j by have := hno j;omega)
    have hpair : 0≤((d j : ℝ)-3)*((d j : ℝ)-4) := by
      by_cases hh : d j≤3
      · have hh' : (d j : ℝ)≤3 := by exact_mod_cast hh
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      · have hh' : (4 : ℝ)≤d j := by exact_mod_cast (show 4≤d j by omega)
        exact mul_nonneg (by linarith) (by linarith)
    simpa only [mul_assoc] using mul_nonneg (sub_nonneg.mpr hd) hpair
  have hs : 0≤∑ j,w j*((d j : ℝ)-1)*((d j : ℝ)-3)*((d j : ℝ)-4) := by
    apply sum_nonneg
    intro j _
    simpa only [mul_assoc] using mul_nonneg (hw j) (hp j)
  linarith
