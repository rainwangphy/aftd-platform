import AFTD.Prelude
import AFTD.Kb.Tcs.ForcedMatchingEdgeBarrierComponentPartition
import AFTD.Kb.Tcs.BoundaryFiveBlocksForcedCrossEdgeIsBridge

/-!
# boundary_five_small_clique_blocks_forced_cross_edge_is_bridge

Topic: graphs   Node: 15c3094e087f

Provenance: helper lemma. OP-1957: structural bridge reduction; experiments 37018 and 37028 test the k=6 case. Experiment 37036 checks k=7.

For every k at least five, in a four-clique boundary partition with the two displayed opposite blocks of size five and minimum degree at least 2k+2, any forced perfect-matching cross edge in a 2k-vertex residual is a bridge of that residual. No connectivity or complementary-matching hypothesis is assumed.
-/

theorem boundary_five_small_clique_blocks_forced_cross_edge_is_bridge
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
    (R : Finset (Fin (4*k))) (hR : R.card=2*k)
    (x y : Fin (4*k)) (hx : x ∈ A) (hy : y ∈ C) (hxy : G.Adj x y)
    (hxR : x ∈ R) (hyR : y ∈ R)
    (hP : ∃ P : (G.induce {v | v ∈ R}).Subgraph, P.IsPerfectMatching)
    (hforced : ¬ ∃ P : ((G.induce {v | v ∈ R}).deleteEdges
      {s(⟨x,hxR⟩,⟨y,hyR⟩)}).Subgraph, P.IsPerfectMatching) :
    ¬ ((G.induce {v | v ∈ R}).deleteEdges
      {s(⟨x,hxR⟩,⟨y,hyR⟩)}).Reachable ⟨x,hxR⟩ ⟨y,hyR⟩ := by
  exact boundary_five_blocks_forced_cross_edge_is_bridge k hk G A B C D hAB hAC hAD hBC hBD hCD hcover hA hC hsizeAB hsizeCD hnoAB hnoCD hdegree R hR x y hx hy hxy hxR hyR hP hforced
