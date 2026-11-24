import AFTD.Prelude
import AFTD.Kb.NumberTheory.WeightedCatalanPoly
import AFTD.Kb.NumberTheory.WeightedCatalanFour

/-!
# weighted_catalan_four_poly_dvd

Topic: elementary_number_theory   Node: 196c8f47bf84

Provenance: helper lemma. arXiv:2611.26953, Section 2, Step 5

For every integer t, 4 divides weighted_catalan_four (weighted_catalan_poly t).
-/

/-- The fourth weighted Catalan number of b_t is divisible by 4. -/
theorem weighted_catalan_four_poly_dvd (t : ℤ) :
    4 ∣ weighted_catalan_four (weighted_catalan_poly t) := by
  use 4752 * t ^ 3 + 2844 * t ^ 2 + 561 * t + 37
  dsimp [weighted_catalan_four, weighted_catalan_poly]
  ring
