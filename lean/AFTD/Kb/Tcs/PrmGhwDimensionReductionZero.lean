import AFTD.Prelude
import AFTD.Kb.Tcs.PrmGHW
import AFTD.Kb.Tcs.FiniteAvoidanceOfThreeBinomialMoments

/-!
# prm_ghw_dimension_reduction_zero

Topic: information   Node: 795521bdce88

Provenance: helper lemma. step towards prm_ghw_dimension_reduction_equality

For any finite field K and parameters e, m, r, the generalized Hamming weight of PRM_K(e + 0*(|K|-1), m) of rank r equals that of PRM_K(e, m - 0).
-/

/-- Base case t = 0 of dimension reduction for generalized Hamming weights of projective Reed-Muller codes. -/
theorem prm_ghw_dimension_reduction_zero (K : Type*) [Field K] [Fintype K]
    (e m r : ℕ) :
    prmGHW K (e + 0 * (Fintype.card K - 1)) m r = prmGHW K e (m - 0) r := by first | exact finite_avoidance_of_three_binomial_moments | (apply finite_avoidance_of_three_binomial_moments <;> assumption) | (apply finite_avoidance_of_three_binomial_moments <;> simp_all) | simpa using finite_avoidance_of_three_binomial_moments | (simp only [prmGHW] at *; first | exact finite_avoidance_of_three_binomial_moments | (apply finite_avoidance_of_three_binomial_moments <;> assumption) | (apply finite_avoidance_of_three_binomial_moments <;> simp_all) | simpa using finite_avoidance_of_three_binomial_moments)
