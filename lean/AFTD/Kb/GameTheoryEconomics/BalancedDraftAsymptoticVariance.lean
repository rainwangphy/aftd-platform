import AFTD.Prelude

/-!
# balanced_draft_asymptotic_variance

Topic: fair_division   Node: 2ce6e1698da2

Provenance: formalization of a published result. Source: arXiv:2611.09685

The theoretical asymptotic variance 4n^2(n-1)/(3(n+1)^2(n+2)) of the scaled normalized utility in balanced drafting of uniform goods.
-/

/-- The asymptotic variance 4n^2(n-1)/(3(n+1)^2(n+2)) of the normalized utility in balanced drafting. -/
noncomputable def balanced_draft_asymptotic_variance (n : ℕ) : ℝ :=
  4 * (n : ℝ)^2 * ((n : ℝ) - 1) / (3 * ((n : ℝ) + 1)^2 * ((n : ℝ) + 2))
