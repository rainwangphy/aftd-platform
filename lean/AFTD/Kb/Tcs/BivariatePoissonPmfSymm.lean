import AFTD.Prelude
import AFTD.Kb.Tcs.BivariatePoissonPmf

/-!
# bivariate_poisson_pmf_symm

Topic: information   Node: eb35d84c6249

Provenance: helper lemma. step towards dual_melas_adjacent_cyclic_patterns_bivariate_poisson_limit

For any natural numbers a and b, bivariate_poisson_pmf a b = bivariate_poisson_pmf b a.
-/

/-- The bivariate Poisson PMF is symmetric in its two arguments. -/
theorem bivariate_poisson_pmf_symm (a b : ℕ) :
    bivariate_poisson_pmf a b = bivariate_poisson_pmf b a := by
  unfold bivariate_poisson_pmf
  rw [min_comm a b, add_comm a b]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ring
