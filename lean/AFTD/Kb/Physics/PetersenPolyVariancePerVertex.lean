import AFTD.Prelude

/-!
# petersen_poly_variance_per_vertex

Topic: statistical_mechanics   Node: 1506cfc513a1

Provenance: formalization of a published result. Source: arXiv:1806.02146

For an activity x, the per-vertex hard-core variance of the Petersen graph computed from its independence polynomial 1 + 10*x + 30*x^2 + 30*x^3 + 5*x^4 as (e2 - e1^2) / 10, where e1 = (10*x + 60*x^2 + 90*x^3 + 20*x^4) / (1 + 10*x + 30*x^2 + 30*x^3 + 5*x^4) and e2 = (10*x + 120*x^2 + 270*x^3 + 80*x^4) / (1 + 10*x + 30*x^2 + 30*x^3 + 5*x^4).
-/

/-- Per-vertex hard-core particle-number variance of the Petersen graph from its independence polynomial. -/
noncomputable def petersen_poly_variance_per_vertex (x : ℝ) : ℝ :=
  let z := 1 + 10 * x + 30 * x^2 + 30 * x^3 + 5 * x^4
  let e1 := (10 * x + 60 * x^2 + 90 * x^3 + 20 * x^4) / z
  let e2 := (10 * x + 120 * x^2 + 270 * x^3 + 80 * x^4) / z
  (e2 - e1^2) / 10
