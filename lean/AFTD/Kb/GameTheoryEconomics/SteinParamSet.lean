import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MuStar

/-!
# stein_param_set

Topic: combinatorial_games   Node: c3900dd04154

Provenance: formalization of a published result. Source: arXiv:2611.05898, Theorem 2.2

The set of triples (d, u, v) of positive natural numbers such that u is odd, mu_star d holds, and d * (u^2 - 2 * v^2)^2 ≤ 4 * u * v (evaluated over the integers).
-/

/-- The parameter set of triples (d, u, v) of positive integers with u odd, mu_star d, and d(u^2 - 2v^2)^2 <= 4uv. -/
def stein_param_set : Set (ℕ × ℕ × ℕ) := {p | let (d, u, v) := p; 0 < d ∧ 0 < u ∧ 0 < v ∧ Odd u ∧ mu_star d ∧ (d : ℤ) * ((u : ℤ)^2 - 2 * (v : ℤ)^2)^2 ≤ 4 * (u : ℤ) * (v : ℤ)}
