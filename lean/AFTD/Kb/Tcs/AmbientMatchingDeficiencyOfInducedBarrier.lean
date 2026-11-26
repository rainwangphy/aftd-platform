import AFTD.Prelude
import AFTD.Kb.Tcs.InducedMatchingLifts
import AFTD.Kb.Tcs.InducedSubgraphBarrierLift

/-!
# ambient_matching_deficiency_of_induced_barrier

Topic: graphs   Node: 87c4c9ad0ab7

Provenance: helper lemma. Balanced-cut k=7 reduction for OP-1957; https://arxiv.org/abs/2611.22690.

The stated matching-deficiency barrier assertion transfers from an induced graph to the ambient graph.
-/

theorem ambient_matching_deficiency_of_induced_barrier
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (R : Finset V) (p : ℕ)
    (hsize : 2*p ≤ R.card)
    (hdef : (¬ ∃ M : (G.induce {v | v ∈ R}).Subgraph, M.IsMatching ∧ p ≤ M.edgeSet.ncard) →
      ∃ Y : Finset {v : V | v ∈ R},
        Fintype.card {v : V | v ∈ R}-2*p+2+Y.card ≤
          ((G.induce {v | v ∈ R}).induce {v | v ∉ Y}).oddComponents.ncard)
    (hnone : ¬ ∃ M : G.Subgraph, M.IsMatching ∧ M.verts ⊆ (R : Set V) ∧ p ≤ M.edgeSet.ncard) :
    ∃ X : Finset V, X ⊆ R ∧
      R.card-2*p+2+X.card ≤ (G.induce {v | v ∈ R ∧ v ∉ X}).oddComponents.ncard := by
  set_option maxHeartbeats 4000000 in
    classical
    have hnone' : ¬ ∃ M : (G.induce {v | v ∈ R}).Subgraph, M.IsMatching ∧ p ≤ M.edgeSet.ncard := by
      rintro ⟨M,hM,hm⟩
      obtain ⟨N,hN,hNR,hNcard⟩ := induced_matching_lifts G {v | v ∈ R} M hM
      exact hnone ⟨N,hN,hNR,by omega⟩
    obtain ⟨Y,hY⟩ := hdef hnone'
    obtain ⟨X,hXR,hXY,heq⟩ := induced_subgraph_barrier_lift G R Y
    have hcard : Fintype.card {v : V | v ∈ R} = R.card := by simp
    refine ⟨X,hXR,?_⟩
    rw [hcard] at hY
    omega
