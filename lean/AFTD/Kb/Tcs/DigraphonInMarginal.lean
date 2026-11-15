import AFTD.Prelude

/-!
# digraphon_in_marginal

Topic: combinatorics   Node: cd84aead80ea

Provenance: formalization of a published result. Source: arXiv:2611.15027 Section 6.1

The in-degree marginal W-(x) of a digraphon W at x is the integral of W(y, x) over y in [0, 1].
-/

/-- The in-degree marginal of a digraphon W at point x. -/
noncomputable def digraphon_in_marginal (W : ℝ → ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in Set.Icc (0 : ℝ) 1, W y x
