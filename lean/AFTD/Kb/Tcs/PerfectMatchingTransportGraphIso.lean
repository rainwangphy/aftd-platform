import AFTD.Prelude

/-!
# perfect_matching_transport_graph_iso

Topic: graphs   Node: 76e0f6ac6b2a

Provenance: helper lemma. OP-1957 factor-critical residual bridge reduction.

A graph isomorphism transports a perfect matching.
-/

theorem perfect_matching_transport_graph_iso {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W)
    (e : G ≃g H) (h : ∃ P : G.Subgraph, P.IsPerfectMatching) :
    ∃ Q : H.Subgraph, Q.IsPerfectMatching := by
  obtain ⟨P,hP⟩ := h
  let Q := P.map e.toHom
  refine ⟨Q, hP.1.map e.toHom e.injective, ?_⟩
  rw [SimpleGraph.Subgraph.isSpanning_iff]
  ext a
  simp only [Q, SimpleGraph.Subgraph.map_verts, hP.2.verts_eq_univ, Set.image_univ,
    Set.mem_univ, iff_true]
  exact ⟨e.symm a, by simp⟩
