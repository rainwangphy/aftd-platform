import AFTD.Prelude
import AFTD.Kb.Tcs.TriangleFreeCardLeFourIsBipartite

/-!
# triangle_free_subcubic_card_le_four_partition

Topic: graphs   Node: 26cfc542e469

Provenance: helper lemma. scout/2611-05178-weighted-max-cut-in-subcubic-graphs.md:1025

Every finite simple graph on at most 4 vertices with maximum degree at most 3 that is triangle-free admits a partition into an independent set L and complement R = Lᶜ such that G[R] is bipartite and for every connected component C of G[R] and every vertex v in L, the induced subgraph on V(C) ∪ {v} is bipartite.
-/

/-- Every finite triangle-free subcubic simple graph on at most 4 vertices admits an independent-bipartite component partition. -/
theorem triangle_free_subcubic_card_le_four_partition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : G.maxDegree ≤ 3) (htf : G.CliqueFree 3)
    (hcard : Fintype.card V ≤ 4) :
    ∃ L : Finset V,
      G.induce (L : Set V) = ⊥ ∧
      (G.induce (Lᶜ : Set V)).IsBipartite ∧
      ∀ C : (G.induce (Lᶜ : Set V)).ConnectedComponent,
        ∀ v ∈ L, (G.induce (Subtype.val '' (C : Set ↑(Lᶜ : Set V)) ∪ {v})).IsBipartite := by
  refine ⟨∅, ?_, ?_, ?_⟩
  · have hset0 : ((∅ : Finset V) : Set V) = (∅ : Set V) := by simp
    rw [hset0]
    haveI : IsEmpty ↥(∅ : Set V) := by rw [Set.isEmpty_coe_sort]
    exact Subsingleton.elim _ _
  · have hb : G.IsBipartite := triangle_free_card_le_four_isBipartite G htf hcard
    have hset : ((∅ : Finset V)ᶜ : Set V) = Set.univ := by simp
    rw [hset]
    rw [show G.induce (Set.univ : Set V) =
      G.comap (Function.Embedding.subtype (· ∈ (Set.univ : Set V))) from rfl]
    exact SimpleGraph.Colorable.of_hom
      (SimpleGraph.Hom.comap (Function.Embedding.subtype (· ∈ (Set.univ : Set V))) G) hb
  · intro C v hv
    simp at hv
