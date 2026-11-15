import AFTD.Prelude

/-!
# digraphon_out_marginal

Topic: combinatorics   Node: b70017cccf0e

Provenance: formalization of a published result. Source: arXiv:2611.15027 Section 6.1

The out-degree marginal W+(x) of a digraphon W at x is the integral of W(x, y) over y in [0, 1].
-/

/-- The out-degree marginal of a digraphon W at point x. -/
noncomputable def digraphon_out_marginal (W : ℝ → ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in Set.Icc (0 : ℝ) 1, W x y
