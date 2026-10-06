import AFTD.Prelude

/-!
# isMatching_sup_disjoint_encard

Topic: graphs   Node: 05d20d51169f

Provenance: helper lemma. step towards konig_matching_vertex_cover_num

For two matchings M and M' in G with disjoint vertex sets, their supremum M ⊔ M' is also a matching, and its edge cardinality is the sum of their edge cardinalities.
-/

/-- The supremum of two matchings with disjoint vertex sets is a matching whose edge count is the sum of their edge counts. -/
theorem isMatching_sup_disjoint_encard {V : Type*} {G : SimpleGraph V} (M M' : SimpleGraph.Subgraph G)
    (hM : M.IsMatching) (hM' : M'.IsMatching) (hd : Disjoint M.verts M'.verts) :
    (M ⊔ M').IsMatching ∧ (M ⊔ M').edgeSet.encard = M.edgeSet.encard + M'.edgeSet.encard := by
  refine ⟨hM.sup hM' ?_, ?_⟩
  · rwa [hM.support_eq_verts, hM'.support_eq_verts]
  · rw [SimpleGraph.Subgraph.edgeSet_sup, Set.encard_union_eq]
    rw [Set.disjoint_left]
    intro e he he'
    induction e using Sym2.ind with
    | h v w =>
      have hvM : v ∈ M.verts := M.mem_verts_of_mem_edge he (Sym2.mem_mk_left v w)
      have hvM' : v ∈ M'.verts := M'.mem_verts_of_mem_edge he' (Sym2.mem_mk_left v w)
      exact Set.disjoint_left.mp hd hvM hvM'
