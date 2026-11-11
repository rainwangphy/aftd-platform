import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.OvercompleteIcaMomentEstimatorA
import AFTD.Kb.ProbabilityStatistics.OvercompleteIcaEmpiricalFourthMoment

/-!
# overcomplete_ica_moment_estimator_exact

Topic: estimation   Node: 1ad9e84c9ddd

Provenance: helper lemma. arXiv:2611.11852 Sec. 5

If the empirical fourth moment of a sample equals the population fourth moment 8 + 4a/q, then the moment estimator a_hat equals a.
-/

/-- The moment estimator recovers the source parameter exactly when the empirical fourth moment matches the population value. -/
theorem overcomplete_ica_moment_estimator_exact (q : ℕ) (n : ℕ) (X : Fin n → ℂ) (a : ℝ) (hq : 0 < q) (hX : overcomplete_ica_empirical_fourth_moment n X = 8 + 4 * a / (q : ℝ)) : overcomplete_ica_moment_estimator_a q n X = a := by
  unfold overcomplete_ica_moment_estimator_a
  rw [hX]
  have hq_ne : (q : ℝ) ≠ 0 := by positivity
  field_simp
  ring
