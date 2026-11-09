import AFTD.Prelude
import AFTD.Kb.Physics.CycleWeightedAdjacencyMatrix

/-!
# cycle_weighted_adjacency_matrix_rank_le

Topic: quantum_mechanics   Node: 1f991eb833f4

Provenance: helper lemma. arXiv:2610.27080, Eq. (13)

For every natural number m, field F, and function t : Fin (2 * m) → F, the rank of cycle_weighted_adjacency_matrix (2 * m) t is at most 2 * m.
-/

/-- The rank of the weighted adjacency matrix of C_{2m} is at most 2m. -/
theorem cycle_weighted_adjacency_matrix_rank_le
    {F : Type*} [Field F] (m : ℕ) (t : Fin (2 * m) → F) :
    (cycle_weighted_adjacency_matrix (2 * m) t).rank ≤ 2 * m := (Matrix.rank_le_card_width _).trans_eq (Fintype.card_fin _)
