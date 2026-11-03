import AFTD.Prelude
import AFTD.Kb.Tcs.BivariatePoissonPmf

/-!
# bivariate_poisson_pmf_nonneg

Topic: information   Node: 025ef8965ea9

Provenance: helper lemma. step towards dual_melas_adjacent_cyclic_patterns_bivariate_poisson_limit

For any natural numbers a and b, 0 ≤ bivariate_poisson_pmf a b.
-/

/-- The bivariate Poisson PMF is nonnegative everywhere. -/
theorem bivariate_poisson_pmf_nonneg (a b : ℕ) :
    0 ≤ bivariate_poisson_pmf a b := by
  unfold bivariate_poisson_pmf
  positivity
