import AFTD.Prelude

/-!
# bivariate_poisson_pmf

Topic: information   Node: 8e319ac9885e

Provenance: formalization of a published result. Source: scout/2610-38017-on-the-b-symbol-weight-distribution-of-dual-melas-codes-and.md:1045

The bivariate Poisson probability mass function bivariate_poisson_pmf a b is defined by Real.exp (-(3/2)) * ∑ j ∈ Finset.range (min a b + 1), ((1 / 2) ^ (a + b - j) / (j! * (a - j)! * (b - j)!)).
-/

/-- The joint PMF of (A+C, B+C) for independent Poisson(1/2) variables A, B, C. -/
noncomputable def bivariate_poisson_pmf (a b : ℕ) : ℝ := Real.exp (-(3/2 : ℝ)) * ∑ j ∈ Finset.range (min a b + 1), ((1 / 2 : ℝ) ^ (a + b - j) / (j.factorial * (a - j).factorial * (b - j).factorial : ℝ))
