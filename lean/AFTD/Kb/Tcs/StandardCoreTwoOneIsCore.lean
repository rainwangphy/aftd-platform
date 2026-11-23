import AFTD.Prelude
import AFTD.Kb.Tcs.LatticeGraphTwoOne
import AFTD.Kb.Tcs.InstFintypeNeighborSetLatticeGraphTwoOne
import AFTD.Kb.Tcs.IsGraphCore
import AFTD.Kb.Tcs.StandardCoreTwoOne

/-!
# standard_core_two_one_is_core

Topic: graphs   Node: b2c72eaca547

Provenance: helper lemma. arXiv:2611.18633 Theorem 4.3

The finset standard_core_two_one is a core in the graph lattice_graph_two_one, that is, is_graph_core lattice_graph_two_one standard_core_two_one holds.
-/

/-- The canonical 12-point set is a core in G_{2,1}. -/
theorem standard_core_two_one_is_core : is_graph_core lattice_graph_two_one standard_core_two_one := by
  unfold is_graph_core
  decide
