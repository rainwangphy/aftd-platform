import AFTD.Prelude

/-!
# thermomajorization_witness_y

Topic: quantum_mechanics   Node: c8961192d511

Provenance: formalization of a published result. Source: OP-2138

For dimension n and rank j, the thermomajorization witness vector y is the uniform distribution on the prefix of length j: y_i = 1 / j for i < j, and 0 otherwise.
-/

/-- Thermomajorization candidate witness vector y for rank j <= n. -/
noncomputable def thermomajorization_witness_y (n : ℕ) (j : ℕ) : Fin n → ℝ :=
  fun i => if (i : ℕ) < j then (1 : ℝ) / (j : ℝ) else 0
