import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding

/-!
# simple_graph_sunflower_packing_witness

Topic: graphs   Node: 5f8b467f176e

Provenance: helper lemma. step towards simple_graph_good_sunflower_forced_base_subpacking_kernel_packed

A witness vertex for a packed petal q: a vertex x outside q such that q \ {r} together with x is a triangle meeting the packed edge union in exactly one edge; defaults to r if no such x exists.
-/

/-- The chosen extra vertex completing q \ {r} to a triangle that meets the packed edge union in exactly one edge; falls back to r when no such vertex exists. -/
noncomputable def simple_graph_sunflower_packing_witness (n : ℕ) (G : SimpleGraph (Fin n)) (P : Finset (Finset (Fin n))) (r : Fin n) (q : Finset (Fin n)) : Fin n := by
  classical
  exact if h : ∃ x : Fin n, x ∉ q ∧ G.IsNClique 3 (insert x (q.erase r)) ∧
      (finite_vertex_set_edge_encoding (insert x (q.erase r)) ∩
        P.biUnion finite_vertex_set_edge_encoding).card = 1
  then Classical.choose h else r
