import AFTD.Prelude
import AFTD.Kb.Tcs.RadialColoring
import AFTD.Kb.Tcs.NormSqThreeApUnit

/-!
# radial_coloring_apply_eq_true

Topic: combinatorics   Node: ee37da8f9b94

Provenance: helper lemma. step towards op_1481_avoidance_three_twenty_one_exceptional_spacings

A point is coloured true by the radial colouring S exactly when its squared norm lies in S.
-/

/-- The defining property of `radial_coloring`, in `↔` form. -/
theorem radial_coloring_apply_eq_true (S : Set ℝ) {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    radial_coloring S x = true ↔ ‖x‖ ^ 2 ∈ S := by first | exact norm_sq_three_ap_unit | (apply norm_sq_three_ap_unit <;> assumption) | (apply norm_sq_three_ap_unit <;> simp_all) | simpa using norm_sq_three_ap_unit | (simp only [radial_coloring] at *; first | exact norm_sq_three_ap_unit | (apply norm_sq_three_ap_unit <;> assumption) | (apply norm_sq_three_ap_unit <;> simp_all) | simpa using norm_sq_three_ap_unit)
