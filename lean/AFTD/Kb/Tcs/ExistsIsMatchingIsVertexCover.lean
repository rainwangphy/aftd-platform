import AFTD.Prelude

/-!
# exists_isMatching_isVertexCover

Topic: graphs   Node: a59cb9d720f0

Provenance: helper lemma. step towards vertex_cover_num_le_two_mul_matching_num

In any finite graph G, there exists a matching M such that M.verts is a vertex cover of G (i.e. an inclusion-maximal matching).
-/

/-- In any finite simple graph G, there exists a matching M whose vertex set M.verts is a vertex cover of G. -/
theorem exists_isMatching_isVertexCover {V : Type*} [Finite V] (G : SimpleGraph V) :
    ∃ M : G.Subgraph, M.IsMatching ∧ G.IsVertexCover M.verts := by
  classical
  have hbot : (⊥ : G.Subgraph).IsMatching := fun v hv => False.elim (by simp at hv)
  obtain ⟨⟨M, hM⟩, hmax⟩ :=
    @Finite.exists_max { M : G.Subgraph // M.IsMatching } ℕ _ ⟨⟨⊥, hbot⟩⟩ _
      (fun M => M.val.verts.ncard)
  refine ⟨M, hM, fun v w hvw => ?_⟩
  by_contra h
  have hv : v ∉ M.verts := fun hvin => h (Or.inl hvin)
  have hw : w ∉ M.verts := fun hwin => h (Or.inr hwin)
  let M' : G.Subgraph := M ⊔ G.subgraphOfAdj hvw
  have hd : Disjoint M.support (G.subgraphOfAdj hvw).support := by
    rw [hM.support_eq_verts, (SimpleGraph.Subgraph.IsMatching.subgraphOfAdj hvw).support_eq_verts,
      SimpleGraph.subgraphOfAdj_verts]
    rw [Set.disjoint_insert_right, Set.disjoint_singleton_right]
    exact ⟨hv, hw⟩
  have hM' : M'.IsMatching := hM.sup (SimpleGraph.Subgraph.IsMatching.subgraphOfAdj hvw) hd
  have hle := hmax ⟨M', hM'⟩
  dsimp at hle
  have hverts : M'.verts = M.verts ∪ {v, w} := by
    change (M ⊔ G.subgraphOfAdj hvw).verts = _
    rw [SimpleGraph.Subgraph.verts_sup, SimpleGraph.subgraphOfAdj_verts]
  have hss : M.verts ⊂ M'.verts := by
    rw [hverts]
    refine ⟨Set.subset_union_left, ?_⟩
    intro heq
    have hvin : v ∈ M.verts ∪ {v, w} := by simp
    have : v ∈ M.verts := heq hvin
    contradiction
  have hlt : M.verts.ncard < M'.verts.ncard := Set.ncard_lt_ncard hss
  omega
