import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.KExtendableEssentialEdgeHasForcedMatchingResidual
import AFTD.Kb.Tcs.BoundaryFiveSmallCliqueBlocksForcedCrossEdgeIsBridge
import AFTD.Kb.Tcs.BoundaryFiveCliqueBlocksFullCrossEssentialEdgeForcesTwins
import AFTD.Kb.Tcs.FourByFiveDefectIncidenceImpossible
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound

/-!
# boundary_five_clique_blocks_full_cross_vertex_has_removable_edge

Topic: graphs   Node: f2103324c918

Provenance: helper lemma. OP-1957: all-k boundary removable-edge route; experiment 37029 is finite evidence.

For k at least five, consider a k-extendible graph on 4k vertices whose four disjoint clique blocks have sizes 5, 2k−5, 5, 2k−5, with the two pairs of blocks anticomplete. If every vertex has degree at least 2k+2, every separating vertex set has size at least 2k, and a vertex of the first five-block is adjacent to all five vertices of the second five-block, then at least one of those five incident cross edges is removable while preserving k-extendibility.
-/

theorem boundary_five_clique_blocks_full_cross_vertex_has_removable_edge
    (k : ℕ) (hk : 5 ≤ k) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hC : C.card=5)
    (hsizeAB : A.card+B.card=2*k) (hsizeCD : C.card+D.card=2*k)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hclique : ∀ T ∈ [A,B,C,D], ∀ u ∈ T, ∀ v ∈ T, u ≠ v → G.Adj u v)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ X U V : Finset (Fin (4*k)), U.Nonempty → V.Nonempty →
      Disjoint X U → Disjoint X V → Disjoint U V → X ∪ U ∪ V = Finset.univ →
      (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v) → 2*k ≤ X.card)
    (hext : is_k_extendable G k) (x : Fin (4*k)) (hx : x ∈ A)
    (hfull : ∀ y ∈ C, G.Adj x y) :
    ∃ y ∈ C, is_k_extendable (G.deleteEdges {s(x,y)}) k := by
  classical
  by_contra hnone
  push Not at hnone
  apply four_by_five_defect_incidence_impossible (A.erase x) C (fun a c => ¬ G.Adj a c)
  · simp [Finset.card_erase_of_mem hx, hA]
  · exact hC
  · intro a ha
    have haA : a ∈ A := (Finset.mem_erase.mp ha).2
    have haB : a ∉ B := fun h => Finset.disjoint_left.mp hAB haA h
    have hanti : ∀ b ∈ B, ¬ G.Adj a b := hnoAB a haA
    have hbudget := anticomplete_neighbor_defect_bound G B a haB hanti (2*k+4) 2 (by simp; omega) (by have := hdegree a; omega)
    apply le_trans (Finset.card_le_card ?_) hbudget
    intro c hc
    simp only [Finset.mem_filter] at hc
    have hcB : c ∉ B := fun h => Finset.disjoint_left.mp hBC h hc.1
    have hca : c ≠ a := fun h => Finset.disjoint_left.mp hAC haA (h ▸ hc.1)
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
    exact ⟨⟨hca, hcB⟩, hc.2⟩
  · intro c hc
    have he := boundary_five_clique_blocks_full_cross_essential_edge_forces_twins k hk G A B C D hAB hAC hAD hBC hBD hCD hcover hA hC hsizeAB hsizeCD hnoAB hnoCD hclique hdegree hsep hext x c hx hc hfull (hnone c hc)
    obtain ⟨p,hp,q,hq,z,hz,hpq,hpx,hqx,hpc,hqc,_,_,_,_⟩ := he
    have hp' : p ∈ (A.erase x).filter (fun a => ¬ G.Adj a c) := by simp [hp,hpx,hpc]
    have hq' : q ∈ (A.erase x).filter (fun a => ¬ G.Adj a c) := by simp [hq,hqx,hqc]
    have h := Finset.one_lt_card.mpr ⟨p,hp',q,hq',hpq⟩
    omega
