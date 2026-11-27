import AFTD.Prelude

/-!
# geometric_gibbs_golden_ratio

Topic: quantum_mechanics   Node: 0c4c69d78cd0

Provenance: formalization of a published result. Source: arXiv:2610.35433

The golden ratio conjugate phi = (sqrt(5) - 1) / 2.
-/

/-- The golden ratio conjugate (sqrt(5) - 1) / 2. -/
noncomputable def geometric_gibbs_golden_ratio : ℝ := (Real.sqrt 5 - 1) / 2
