import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.OvercompleteIcaEmpiricalFourthMoment

/-!
# overcomplete_ica_moment_estimator_a

Topic: estimation   Node: 0a605c9d8106

Provenance: formalization of a published result. Source: arXiv:2611.11852 Sec. 5

In the equally spaced overcomplete ICA model with q sources, the moment estimator for the source parameter a is (q / 4) * ((1/n) * sum_{i=1}^n ||X_i||^4 - 8).
-/

/-- Moment estimator for source kurtosis parameter a from the empirical fourth moment. -/
noncomputable def overcomplete_ica_moment_estimator_a (q : ℕ) (n : ℕ) (X : Fin n → ℂ) : ℝ := (q : ℝ) / 4 * (overcomplete_ica_empirical_fourth_moment n X - 8)
