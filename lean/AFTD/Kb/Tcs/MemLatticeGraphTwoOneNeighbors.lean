import AFTD.Prelude
import AFTD.Kb.Tcs.LatticeGraphTwoOne
import AFTD.Kb.Tcs.LatticeGraphTwoOneNeighbors
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# mem_lattice_graph_two_one_neighbors

Topic: graphs   Node: d1a2e0b012c3

Provenance: helper lemma. arXiv:2611.18633 Section 1

For v u : ℤ × ℤ, u belongs to the finset lattice_graph_two_one_neighbors v if and only if lattice_graph_two_one.Adj v u.
-/

/-- Equivalence between membership in the neighbor finset and adjacency in G_{2,1}. -/
theorem mem_lattice_graph_two_one_neighbors (v u : ℤ × ℤ) : u ∈ lattice_graph_two_one_neighbors v ↔ lattice_graph_two_one.Adj v u := by
  simp [lattice_graph_two_one_neighbors, lattice_graph_two_one, lattice_ball_one,
    Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨Ne.symm h1, by omega, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨Ne.symm h1, by omega, by omega⟩
