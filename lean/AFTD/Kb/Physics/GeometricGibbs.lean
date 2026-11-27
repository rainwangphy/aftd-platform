import AFTD.Prelude

/-!
# geometric_gibbs

Topic: quantum_mechanics   Node: 98733b0d3428

Provenance: formalization of a published result. Source: arXiv:2610.35433

For parameter 0 < q < 1 and dimension N, the geometric Gibbs distribution g_i is (1-q) * q^i / (1-q^N) for i ∈ Fin N.
-/

/-- The geometric Gibbs distribution on N levels with ratio q. -/
noncomputable def geometric_gibbs (N : ℕ) (q : ℝ) (i : Fin N) : ℝ := (1 - q) * q ^ (i : ℕ) / (1 - q ^ N)
