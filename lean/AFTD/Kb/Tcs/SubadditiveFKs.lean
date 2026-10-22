import AFTD.Prelude

/-!
# subadditive_f_ks

Topic: information   Node: 36919ed27a58

Provenance: formalization of a published result. Source: arXiv:2610.21231, Corollary 1

For a twice differentiable function s, the associated K_s function is K_s(x) = s(x) + 2(s'(x))^2/(-s''(x)).
-/

/-- The K_s function associated to s, defined as K_s(x) = s(x) + 2 (s'(x))^2 / (-s''(x)). -/
noncomputable def subadditive_f_ks (s : ℝ → ℝ) (x : ℝ) : ℝ := s x + 2 * (deriv s x) ^ 2 / (- deriv (deriv s) x)
