import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.KExtendableEssentialEdgeHasForcedMatchingResidual
import AFTD.Kb.Tcs.BoundaryFiveSmallCliqueBlocksForcedCrossEdgeIsBridge
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound
import AFTD.Kb.Tcs.BoundaryFiveCliqueBlocksFullCrossEssentialEdgeForcesTwinsOfBridge
import AFTD.Kb.Tcs.BoundaryFiveBlocksForcedCrossEdgeIsBridge

/-!
# boundary_five_clique_blocks_full_cross_essential_edge_forces_twins

Topic: graphs   Node: 23afbc131fac

Provenance: helper lemma. OP-1957: structural classification of forced bridge witnesses for a full-cross vertex.

In the displayed size-five four-clique boundary partition of a 2k-connected k-extendible graph with degree at least 2k+2, suppose x in the first five-block is adjacent to all of the second five-block and an edge xy to that block is essential. Then two other vertices p and q of the first block are true twins; both miss y and a common vertex z of the opposite large block, and x also misses z.
-/

theorem boundary_five_clique_blocks_full_cross_essential_edge_forces_twins
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
    (hext : is_k_extendable G k) (x y : Fin (4*k)) (hx : x ∈ A) (hy : y ∈ C)
    (hfull : ∀ w ∈ C, G.Adj x w)
    (hess : ¬ is_k_extendable (G.deleteEdges {s(x,y)}) k) :
    ∃ p ∈ A, ∃ q ∈ A, ∃ z ∈ D,
      p ≠ q ∧ p ≠ x ∧ q ≠ x ∧ ¬ G.Adj p y ∧ ¬ G.Adj q y ∧
      ¬ G.Adj x z ∧ ¬ G.Adj p z ∧ ¬ G.Adj q z ∧
      (∀ w, w ≠ p → w ≠ q → (G.Adj p w ↔ G.Adj q w)) := by
  apply boundary_five_clique_blocks_full_cross_essential_edge_forces_twins_of_bridge k hk G A B C D hAB hAC hAD hBC hBD hCD hcover hA hC hsizeAB hsizeCD hnoAB hnoCD hclique hdegree hsep hext x y hx hy hfull hess
  intro R hR hxR hyR hP hforced
  exact boundary_five_blocks_forced_cross_edge_is_bridge k hk G A B C D hAB hAC hAD hBC hBD hCD hcover hA hC hsizeAB hsizeCD hnoAB hnoCD hdegree R hR x y hx hy (hfull y hy) hxR hyR hP hforced
