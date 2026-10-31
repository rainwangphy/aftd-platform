import AFTD.Prelude

/-!
# bell_network_lambda

Topic: quantum   Node: 3326c504c213

Provenance: formalization of a published result. Source: arXiv:2610.35838 Eq. 11

For vectors u, v in R^3, Lambda(u, v) is defined as (1/2) * (s + sqrt(s^2 - 4 * (u . v)^2)) where s = |u|^2 + |v|^2.
-/

/-- The two-copy closed-network Bell measurement function Lambda(u, v) on two 3-vectors. -/
noncomputable def bell_network_lambda (u v : Fin 3 → ℝ) : ℝ :=
  let s := (u ⬝ᵥ u) + (v ⬝ᵥ v)
  (1 / 2 : ℝ) * (s + Real.sqrt (s ^ 2 - 4 * (u ⬝ᵥ v) ^ 2))
