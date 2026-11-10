import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphSunflowerPackingWitness
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding

/-!
# simple_graph_sunflower_packing_kernel_graph

Topic: graphs   Node: 702f123183f1

Provenance: helper lemma. step towards simple_graph_good_sunflower_forced_base_subpacking_kernel_packed

The kernel graph H: every edge of G with both endpoints in the union of the petals of Q, plus, for each petal q of Q, the two edges that join its witness vertex to q \ {r}.
-/

/-- The kernel graph: all edges of G inside the union of the packed petals Q, together with the two witness edges of each q ∈ Q. -/
noncomputable def simple_graph_sunflower_packing_kernel_graph (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P : Finset (Finset (Fin n))) (r : Fin n) (Q : Finset (Finset (Fin n))) : SimpleGraph (Fin n) := SimpleGraph.fromEdgeSet ↑((G.edgeFinset ∩ finite_vertex_set_edge_encoding (Q.biUnion id)) ∪
    Q.biUnion (fun q => finite_vertex_set_edge_encoding
      (insert (simple_graph_sunflower_packing_witness n G P r q) (q.erase r))))
