import AFTD.Prelude

/-!
# subcubic_isAcyclic_exists_independent_bipartite_component_partition

Topic: graphs   Node: 9230d3e2c4b8

Provenance: helper lemma. scout/2611-05178-weighted-max-cut-in-subcubic-graphs.md:1025

Every finite simple graph with maximum degree at most 3 that is acyclic admits a partition into an independent set L and complement R = Lᶜ such that G[R] is bipartite and for every connected component C of G[R] and every vertex v in L, the induced subgraph on V(C) ∪ {v} is bipartite.
-/

/-- Every finite acyclic subcubic simple graph admits an independent-bipartite component partition. -/
theorem subcubic_isAcyclic_exists_independent_bipartite_component_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : G.maxDegree ≤ 3) (hforest : G.IsAcyclic) :
    ∃ L : Finset V,
      G.induce (L : Set V) = ⊥ ∧
      (G.induce (Lᶜ : Set V)).IsBipartite ∧
      ∀ C : (G.induce (Lᶜ : Set V)).ConnectedComponent,
        ∀ v ∈ L, (G.induce (Subtype.val '' (C : Set ↑(Lᶜ : Set V)) ∪ {v})).IsBipartite := by
  refine ⟨∅, ?_, ?_, ?_⟩
  · ext ⟨x, hx⟩
    simp at hx
  · exact (hforest.induce _).isBipartite
  · intro C v hv
    simp at hv
