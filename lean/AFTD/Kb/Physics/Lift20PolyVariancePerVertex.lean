import AFTD.Prelude

/-!
# lift20_poly_variance_per_vertex

Topic: statistical_mechanics   Node: b2562c2dcb1b

Provenance: formalization of a published result. Source: arXiv:1806.02146

For an activity x, the per-vertex hard-core variance of the 20-vertex Petersen 2-lift computed from its independence polynomial Q(x) = 1 + 20*x + 160*x^2 + 660*x^3 + 1510*x^4 + 1912*x^5 + 1240*x^6 + 320*x^7 + 5*x^8 as (e2 - e1^2) / 20, where e1 = (20*x + 320*x^2 + 1980*x^3 + 6040*x^4 + 9560*x^5 + 7440*x^6 + 2240*x^7 + 40*x^8) / Q(x) and e2 = (20*x + 640*x^2 + 5940*x^3 + 24160*x^4 + 47800*x^5 + 44640*x^6 + 15680*x^7 + 320*x^8) / Q(x).
-/

/-- Per-vertex hard-core particle-number variance of the 20-vertex Petersen two-lift from its independence polynomial. -/
noncomputable def lift20_poly_variance_per_vertex (x : ℝ) : ℝ :=
  let z := 1 + 20 * x + 160 * x^2 + 660 * x^3 + 1510 * x^4 + 1912 * x^5 + 1240 * x^6 + 320 * x^7 + 5 * x^8
  let e1 := (20 * x + 320 * x^2 + 1980 * x^3 + 6040 * x^4 + 9560 * x^5 + 7440 * x^6 + 2240 * x^7 + 40 * x^8) / z
  let e2 := (20 * x + 640 * x^2 + 5940 * x^3 + 24160 * x^4 + 47800 * x^5 + 44640 * x^6 + 15680 * x^7 + 320 * x^8) / z
  (e2 - e1^2) / 20
