import AFTD.Prelude

/-!
# thermomajorization_probe_gap_error

Topic: quantum_mechanics   Node: aa0aa41b2fa3

Provenance: formalization of a published result. Source: arXiv:2610.35433

For natural numbers a, b, and j, the thermomajorization probe gap error thermomajorization_probe_gap_error a b j is defined as ((j - a : ℝ) * (b - j : ℝ)) / ((j : ℝ) * (b - a : ℝ)).
-/

/-- The sharp missed error (j - a)(b - j) / (j(b - a)) for an unprobed rank j between adjacent probed ranks a and b. -/
noncomputable def thermomajorization_probe_gap_error (a b j : ℕ) : ℝ := ((j - a : ℝ) * (b - j : ℝ)) / ((j : ℝ) * (b - a : ℝ))
