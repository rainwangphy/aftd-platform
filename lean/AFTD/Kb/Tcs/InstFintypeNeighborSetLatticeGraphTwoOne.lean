import AFTD.Prelude
import AFTD.Kb.Tcs.LatticeGraphTwoOne
import AFTD.Kb.Tcs.LatticeGraphTwoOneNeighbors
import AFTD.Kb.Tcs.LatticeBallOne
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# instFintypeNeighborSetLatticeGraphTwoOne

Topic: graphs   Node: fd3e89c8d7fc

Provenance: formalization of a published result. Source: arXiv:2611.18633 Section 1

For any vertex v : ℤ × ℤ, the neighbor set lattice_graph_two_one.neighborSet v is finite, with a Fintype instance.
-/

/-- Fintype instance for the neighbor set of any vertex in G_{2,1}. -/
instance instFintypeNeighborSetLatticeGraphTwoOne (v : ℤ × ℤ) : Fintype (lattice_graph_two_one.neighborSet v) := Fintype.ofFinset (lattice_graph_two_one_neighbors v) fun u => by
  dsimp [lattice_graph_two_one_neighbors, lattice_ball_one, lattice_graph_two_one]
  simp only [Finset.mem_erase, Finset.mem_product, Finset.mem_Icc, SimpleGraph.mem_neighborSet]
  constructor
  · rintro ⟨hne, ⟨h1l, h1u⟩, ⟨h2l, h2u⟩⟩
    refine ⟨Ne.symm hne, ?_, ?_⟩
    · rw [abs_le]; constructor <;> omega
    · rw [abs_le]; constructor <;> omega
  · rintro ⟨hne, h1, h2⟩
    rw [abs_le] at h1 h2
    refine ⟨Ne.symm hne, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
