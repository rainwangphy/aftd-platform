import AFTD.Prelude

/-!
# digraphon_symmetrization

Topic: combinatorics   Node: ff13695f9518

Provenance: formalization of a published result. Source: arXiv:2611.15027 Section 2

Given a function W : ℝ → ℝ → ℝ, its symmetrization digraphon_symmetrization W is the function fun x y => (W x y + W y x) / 2.
-/

/-- Symmetrization S = (W + Wᵀ)/2 of a digraphon. -/
noncomputable def digraphon_symmetrization (W : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ := fun x y => (W x y + W y x) / 2
