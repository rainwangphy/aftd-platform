import AFTD.Prelude
import AFTD.Kb.Physics.CycleWeightedAdjacencyMatrix

/-!
# cycle_weighted_adjacency_matrix_diag

Topic: quantum_mechanics   Node: 6c77e9e6142f

Provenance: helper lemma. folklore

For any type α with AddZeroClass, any natural number n, any function t : Fin n → α, and any vertex i : Fin n, the diagonal entry cycle_weighted_adjacency_matrix n t i i equals 0.
-/

/-- The diagonal entries of the cycle weighted adjacency matrix are zero. -/
theorem cycle_weighted_adjacency_matrix_diag {α : Type*} [AddZeroClass α] (n : ℕ) (t : Fin n → α)
    (i : Fin n) :
    cycle_weighted_adjacency_matrix n t i i = 0 := by
  simp [cycle_weighted_adjacency_matrix, SimpleGraph.irrefl]
