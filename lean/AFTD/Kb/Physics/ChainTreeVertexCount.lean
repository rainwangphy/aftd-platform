import AFTD.Prelude

/-!
# chain_tree_vertex_count

Topic: quantum_mechanics   Node: 6dd30b199a8e

Provenance: helper lemma. folklore

For every integer k with 1 ≤ k, the Cartesian product type Fin k × Fin 16 has cardinality Fintype.card (Fin k × Fin 16) = 16 * k.
-/

/-- The vertex type of the k-copy chain tree on 16-vertex gadgets has cardinality 16k. -/
theorem chain_tree_vertex_count (k : ℕ) (hk : 1 ≤ k) : Fintype.card (Fin k × Fin 16) = 16 * k := by
  simp [mul_comm]
