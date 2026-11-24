import AFTD.Prelude
import AFTD.Kb.NumberTheory.WeightedCatalanPoly
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddDvdEq
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# weighted_catalan_poly_zero

Topic: elementary_number_theory   Node: 50e31942ed6a

Provenance: helper lemma. arXiv:2611.26953, Lemma 7 proof

For every integer t, the polynomial b_t satisfies b_t(0) = 1.
-/

/-- The polynomial b_t evaluates to 1 at 0. -/
theorem weighted_catalan_poly_zero (t : ℤ) : weighted_catalan_poly t 0 = 1 := by first | exact postage_stamp_number_neg_two_of_odd_dvd_eq | (apply postage_stamp_number_neg_two_of_odd_dvd_eq <;> assumption) | (apply postage_stamp_number_neg_two_of_odd_dvd_eq <;> simp_all) | simpa using postage_stamp_number_neg_two_of_odd_dvd_eq | (simp only [weighted_catalan_poly] at *; first | exact postage_stamp_number_neg_two_of_odd_dvd_eq | (apply postage_stamp_number_neg_two_of_odd_dvd_eq <;> assumption) | (apply postage_stamp_number_neg_two_of_odd_dvd_eq <;> simp_all) | simpa using postage_stamp_number_neg_two_of_odd_dvd_eq)
