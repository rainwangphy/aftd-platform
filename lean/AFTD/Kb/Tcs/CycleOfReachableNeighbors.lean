import AFTD.Prelude

/-!
# cycle_of_reachable_neighbors

Topic: graphs   Node: 464225e71c5e

Provenance: helper lemma. arXiv:2610.26912: Theorem 2.22 -- Vertex Removal and Vertex-Edge Domination

If two distinct neighbors u and w of a vertex v in a simple graph G are reachable from each other in the induced subgraph G - v obtained by deleting v, then there exists a cycle in G from v to v.
-/

/-- Two distinct neighbors of v reachable in G - v determine a cycle containing v. -/
lemma cycle_of_reachable_neighbors {V : Type*} (G : SimpleGraph V) (v u w : V)
    (huv : G.Adj v u) (hvw : G.Adj v w) (hne : u ≠ w)
    (hreach : (G.induce ({v}ᶜ : Set V)).Reachable ⟨u, (G.ne_of_adj huv).symm⟩ ⟨w, (G.ne_of_adj hvw).symm⟩) :
    ∃ (p : G.Walk v v), p.IsCycle := by
  obtain ⟨q, hq⟩ := SimpleGraph.Reachable.exists_isPath hreach
  let f : G.induce ({v}ᶜ : Set V) ↪g G := SimpleGraph.Embedding.induce ({v}ᶜ : Set V)
  let p₁ : G.Walk u w := q.map f.toHom
  have hq_map : p₁.IsPath := (SimpleGraph.Walk.isPath_map_iff_of_injective f.injective).mpr hq
  have hv : v ∉ p₁.support := by
    intro h
    have h' : v ∈ (q.map f.toHom).support := h
    rw [SimpleGraph.Walk.support_map, List.mem_map] at h'
    rcases h' with ⟨x, _, hx⟩
    exact x.2 hx
  let p₂ : G.Walk u v := p₁.concat hvw.symm
  have hp₂ : p₂.IsPath := by
    rw [SimpleGraph.Walk.concat_isPath_iff]
    exact ⟨hq_map, hv⟩
  have he : s(v, u) ∉ p₂.edges := by
    rw [SimpleGraph.Walk.edges_concat]
    intro he'
    rw [List.concat_eq_append, List.mem_append, List.mem_singleton] at he'
    rcases he' with he1 | he2
    · have := SimpleGraph.Walk.fst_mem_support_of_mem_edges p₁ he1
      exact hv this
    · rw [Sym2.eq_iff] at he2
      rcases he2 with ⟨h1, h2⟩ | ⟨-, h2⟩
      · exact (G.ne_of_adj huv) h2.symm
      · exact hne h2
  refine ⟨SimpleGraph.Walk.cons huv p₂, ?_⟩
  rw [SimpleGraph.Walk.cons_isCycle_iff]
  exact ⟨hp₂, he⟩
