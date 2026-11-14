import AFTD.Prelude
import AFTD.Kb.Tcs.RingDiamondGraph

/-!
# ring_diamond_graph_edge_fintype

Topic: combinatorics   Node: 29033b327695

Provenance: helper lemma. step towards near_minimum_cycle_counting_bound_real_exponent

The edge set of the 60-vertex ring of 20 diamonds is finite, so `ring_diamond_graph.edgeFinset` is available.
-/

/-- The edge set of the ring of diamonds is finite (60 vertices, so at most 1770 edges). -/
noncomputable instance ring_diamond_graph_edge_fintype : Fintype ↥ring_diamond_graph.edgeSet := Fintype.ofFinite _
