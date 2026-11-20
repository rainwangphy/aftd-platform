import AFTD.Prelude

/-!
# perfect_matching_forced_edge_in_every_matching

Topic: graphs   Node: 773785b43e0d

Provenance: helper lemma. OP-1957 factor-critical forced-bridge shore construction.

If deleting an edge destroys all perfect matchings, every perfect matching contains it.
-/

theorem perfect_matching_forced_edge_in_every_matching {V : Type*} (G : SimpleGraph V) (x z : V)
    (hforced : ¬ ∃ Q : (G.deleteEdges {s(x,z)}).Subgraph, Q.IsPerfectMatching)
    (P : G.Subgraph) (hP : P.IsPerfectMatching) : P.Adj x z := by
  classical
  by_contra hno
  have hle : P.spanningCoe ≤ G.deleteEdges {s(x,z)} := by
    intro a b hab
    apply SimpleGraph.deleteEdges_adj.mpr
    refine ⟨P.adj_sub hab, ?_⟩
    simp only [Set.mem_singleton_iff, Sym2.eq_iff, not_or, not_and]
    constructor
    · intro ha hb
      exact hno (ha ▸ hb ▸ hab)
    · intro ha hb
      exact hno (hb ▸ ha ▸ hab.symm)
  exact hforced ⟨SimpleGraph.toSubgraph P.spanningCoe hle,
    (SimpleGraph.Subgraph.IsPerfectMatching.toSubgraph_iff hle).mpr hP⟩
