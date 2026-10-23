import AFTD.Prelude

/-!
# subadditive_f_weight

Topic: information   Node: aede1cd5b2c8

Provenance: formalization of a published result. Source: arXiv:2610.21231 (On the subadditivity of mutual f-information), Theorem 1: g(x) = x² f''(x)

The weight g(x) = x² f''(x) attached to a generator f in Theorem 1 of arXiv:2610.21231 (f'' is the iterated derivative `deriv (deriv f)`).
-/

noncomputable def subadditive_f_weight (f : ℝ → ℝ) (x : ℝ) : ℝ := x ^ 2 * deriv (deriv f) x
