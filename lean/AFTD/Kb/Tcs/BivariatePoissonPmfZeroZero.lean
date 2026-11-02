import AFTD.Prelude
import AFTD.Kb.Tcs.BivariatePoissonPmf

/-!
# bivariate_poisson_pmf_zero_zero

Topic: information   Node: bab066d1f532

Provenance: helper lemma. folklore

The bivariate Poisson probability mass function bivariate_poisson_pmf with independent Poisson(1/2) components evaluated at (0, 0) is equal to Real.exp (-(3/2)).
-/

/-- The bivariate Poisson PMF with mean-1/2 components at (0, 0) equals exp(-3/2). -/
theorem bivariate_poisson_pmf_zero_zero : bivariate_poisson_pmf 0 0 = Real.exp (-(3/2 : ℝ)) := by
  simp [bivariate_poisson_pmf]
