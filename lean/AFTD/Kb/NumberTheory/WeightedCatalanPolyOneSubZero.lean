import AFTD.Prelude
import AFTD.Kb.NumberTheory.WeightedCatalanPoly
import AFTD.Kb.NumberTheory.WeightedCatalanPolyZero

/-!
# weighted_catalan_poly_one_sub_zero

Topic: elementary_number_theory   Node: 6ace862f85b5

Provenance: helper lemma. arXiv:2611.26953, Lemma 7 proof

For every integer t, the difference b_t(1) - b_t(0) is equal to 4 * t.
-/

/-- The difference b_t(1) - b_t(0) equals 4t. -/
theorem weighted_catalan_poly_one_sub_zero (t : ℤ) :
    weighted_catalan_poly t 1 - weighted_catalan_poly t 0 = 4 * t := by first | exact weighted_catalan_poly_zero | (apply weighted_catalan_poly_zero <;> assumption) | (apply weighted_catalan_poly_zero <;> simp_all) | simpa using weighted_catalan_poly_zero | (simp only [weighted_catalan_poly] at *; first | exact weighted_catalan_poly_zero | (apply weighted_catalan_poly_zero <;> assumption) | (apply weighted_catalan_poly_zero <;> simp_all) | simpa using weighted_catalan_poly_zero)
