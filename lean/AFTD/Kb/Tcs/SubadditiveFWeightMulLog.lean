import AFTD.Prelude
import AFTD.Kb.Tcs.SubadditiveFWeight

/-!
# subadditive_f_weight_mul_log

Topic: information   Node: 7da9e7222db9

Provenance: helper lemma. sanity lemma for subadditive_f_weight

Sanity: for the Shannon generator f(x) = x log x, the weight is g(x) = x² · (1/x) = x for x > 0.
-/

theorem subadditive_f_weight_mul_log {x : ℝ} (hx : 0 < x) :
    subadditive_f_weight (fun y => y * Real.log y) x = x := by
  have heq : deriv (fun y => y * Real.log y) =ᶠ[nhds x] fun y => Real.log y + 1 := by
    filter_upwards [lt_mem_nhds hx] with y hy
    exact (Real.hasDerivAt_mul_log (ne_of_gt hy)).deriv
  have h2 : HasDerivAt (deriv (fun y => y * Real.log y)) x⁻¹ x :=
    (((Real.hasDerivAt_log (ne_of_gt hx)).add_const 1).congr_of_eventuallyEq heq)
  unfold subadditive_f_weight
  rw [h2.deriv]
  field_simp
