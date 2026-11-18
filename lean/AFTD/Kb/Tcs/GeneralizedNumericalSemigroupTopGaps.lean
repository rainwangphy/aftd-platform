import AFTD.Prelude
import AFTD.Kb.Tcs.GeneralizedNumericalSemigroup
import AFTD.Kb.Tcs.GeneralizedNumericalSemigroupTop
import AFTD.Kb.Tcs.GeneralizedNumericalSemigroupGaps
import AFTD.Kb.Tcs.TwoPowEqSuccIff

/-!
# generalized_numerical_semigroup_top_gaps

Topic: combinatorics   Node: ab86333b3b42

Provenance: helper lemma. arXiv:2611.20086 Definition 2.1

The gap set of the full generalized numerical semigroup in dimension d is empty.
-/

/-- The gap set of the full generalized numerical semigroup is empty. -/
theorem generalized_numerical_semigroup_top_gaps (d : ℕ) : generalized_numerical_semigroup_gaps (generalized_numerical_semigroup_top d) = ∅ := by first | exact two_pow_eq_succ_iff | (apply two_pow_eq_succ_iff <;> assumption) | (apply two_pow_eq_succ_iff <;> simp_all) | simpa using two_pow_eq_succ_iff | (simp only [generalized_numerical_semigroup_gaps, generalized_numerical_semigroup_top] at *; first | exact two_pow_eq_succ_iff | (apply two_pow_eq_succ_iff <;> assumption) | (apply two_pow_eq_succ_iff <;> simp_all) | simpa using two_pow_eq_succ_iff)
