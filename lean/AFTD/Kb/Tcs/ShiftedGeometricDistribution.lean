import AFTD.Prelude

/-!
# shifted_geometric_distribution

Topic: information   Node: 0d53849987d4

Provenance: formalization of a published result. Source: arXiv:2611.16066, Theorem 5.1

The shifted geometric distribution G_L(s) with base parameter a supported on s ≥ L is equal to (1 - a) * a^(s - L) for s ≥ L and 0 otherwise.
-/

/-- The shifted geometric distribution G_L with base parameter a on ℤ supported on integers s ≥ L. -/
noncomputable def shifted_geometric_distribution (a : ℝ) (L : ℤ) (s : ℤ) : ℝ := if L ≤ s then (1 - a) * a ^ (s - L) else 0
