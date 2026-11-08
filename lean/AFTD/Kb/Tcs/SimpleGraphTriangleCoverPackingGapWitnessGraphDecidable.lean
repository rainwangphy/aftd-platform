import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverPackingGapDeletedEdges
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverPackingGapWitnessGraph

/-!
# simple_graph_triangle_cover_packing_gap_witness_graph_decidable

Topic: graphs   Node: ee59981b360e

Provenance: helper lemma. step towards simple_graph_minimum_triangle_cover_outside_maximum_packing_support

Adjacency in the witness graph is decidable, so the finite computations can be run by `decide`.
-/

/-- Decidable adjacency for the witness graph. -/
instance simple_graph_triangle_cover_packing_gap_witness_graph_decidable : DecidableRel simple_graph_triangle_cover_packing_gap_witness_graph.Adj := fun a b => by
  show Decidable (a ≠ b ∧ Sym2.mk a b ∉ simple_graph_triangle_cover_packing_gap_deleted_edges)
  infer_instance
