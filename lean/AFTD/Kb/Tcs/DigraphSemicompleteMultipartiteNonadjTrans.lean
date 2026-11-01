import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsSemicompleteMultipartite

/-!
# digraph_semicomplete_multipartite_nonadj_trans

Topic: graphs   Node: 6b9a21981edd

Provenance: helper lemma. step towards digraph_four_strong_semicomplete_multipartite_nonadjacent_pairs_linked

In a semicomplete multipartite digraph D, non-adjacency in both directions is transitive among pairwise distinct vertices.
-/

/-- In a semicomplete multipartite digraph D, non-adjacency in both directions is transitive among pairwise distinct vertices. -/
theorem digraph_semicomplete_multipartite_nonadj_trans {V : Type*} (D : Digraph V)
    (hmulti : digraph_is_semicomplete_multipartite D)
    {u v w : V} (huv : ¬ D.Adj u v ∧ ¬ D.Adj v u) (hvw : ¬ D.Adj v w ∧ ¬ D.Adj w v) (h : u ≠ w) :
    ¬ D.Adj u w ∧ ¬ D.Adj w u := by
  obtain ⟨-, htrans⟩ := hmulti
  have h1 : ¬ D.toSimpleGraphInclusive.Adj u v := by
    simp [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj, huv]
  have h2 : ¬ D.toSimpleGraphInclusive.Adj v w := by
    simp [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj, hvw]
  have h3 : ¬ D.toSimpleGraphInclusive.Adj u w := @IsTrans.trans V _ htrans u v w h1 h2
  rw [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj] at h3
  tauto
