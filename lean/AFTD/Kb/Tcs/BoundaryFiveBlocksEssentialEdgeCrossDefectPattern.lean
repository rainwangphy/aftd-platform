import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.KExtendableEssentialEdgeHasForcedMatchingResidual
import AFTD.Kb.Tcs.BoundaryFiveBlocksForcedCrossEdgeIsBridge
import AFTD.Kb.Tcs.PerfectMatchingForcedEdgeInEveryMatching
import AFTD.Kb.Tcs.PerfectMatchingBridgeEvenShoresOnFinset
import AFTD.Kb.Tcs.BoundaryFiveBlocksVertexNonneighborDefects
import AFTD.Kb.Tcs.FinsetCardEqSumFourBlockInter
import AFTD.Kb.Tcs.BoundaryFiveBlocksStrongShoreSeparatorBound
import AFTD.Kb.Tcs.BoundaryFiveBlocksBridgeShoreDefectConstraints
import AFTD.Kb.Tcs.BoundaryFiveBlocksShortCShoreArithmetic
import AFTD.Kb.Tcs.BoundaryFiveBlocksTwoDefectShoreArithmetic
import AFTD.Kb.Tcs.BoundaryFiveBlocksBridgeShoreDefectPattern
import AFTD.Kb.Tcs.BoundaryFiveBlocksDefectFromShoreShape

/-!
# boundary_five_blocks_essential_edge_cross_defect_pattern

Topic: graphs   Node: 0e51d15bcff0

Provenance: helper lemma. OP-1957: all-k nonclique essential-edge classification using a strengthened separator.

In the displayed four-block partition with both selected blocks of size five, minimum degree at least 2k+2, a separator property and k-extendibility, an essential cross edge xy obeys two restrictions: if x misses two vertices of the opposite small block each of those vertices misses exactly one vertex of the first block; if x misses at most one vertex of the opposite small block, y misses exactly two vertices of the first. No block is assumed to be a clique.
-/

theorem boundary_five_blocks_essential_edge_cross_defect_pattern
    (k : ℕ) (hk : 5 ≤ k) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hC : C.card=5)
    (hsizeAB : A.card+B.card=2*k) (hsizeCD : C.card+D.card=2*k)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ X U V : Finset (Fin (4*k)), U.Nonempty → V.Nonempty →
      Disjoint X U → Disjoint X V → Disjoint U V → X ∪ U ∪ V = Finset.univ →
      (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v) → 2*k ≤ X.card)
    (hext : is_k_extendable G k) (x y : Fin (4*k)) (hx : x ∈ A) (hy : y ∈ C)
    (hxy : G.Adj x y) (hess : ¬ is_k_extendable (G.deleteEdges {s(x,y)}) k) :
    (((C.filter (fun w => ¬ G.Adj x w)).card = 2) →
      ∀ u ∈ C, ¬ G.Adj x u → (A.filter (fun v => ¬ G.Adj v u)).card = 1) ∧
    (((C.filter (fun w => ¬ G.Adj x w)).card ≤ 1) →
      (A.filter (fun v => ¬ G.Adj v y)).card = 2) := by
  classical
  obtain ⟨R, hRsum, hxR, hyR, ⟨P,hP⟩, hforced⟩ :=
    k_extendable_essential_edge_has_forced_matching_residual (4*k) k G x y hxy hext hess
  have hR : R.card = 2*k := by omega
  have hnr := boundary_five_blocks_forced_cross_edge_is_bridge k hk G A B C D
    hAB hAC hAD hBC hBD hCD hcover hA hC hsizeAB hsizeCD hnoAB hnoCD hdegree
    R hR x y hx hy hxy hxR hyR ⟨P,hP⟩ hforced
  have hPxy : P.Adj ⟨x,hxR⟩ ⟨y,hyR⟩ :=
    perfect_matching_forced_edge_in_every_matching _ _ _ hforced P hP
  obtain ⟨Q, W, hQW, hcov, hxQ, hyQ, hxW, hyW, hqe, hwe, hyQadj, hxWadj, hQWadj⟩ :=
    perfect_matching_bridge_even_shores_on_finset G R x y hxR hyR P hP hPxy hnr
  have hshape := boundary_five_blocks_bridge_shore_defect_pattern k hk G A B C D
    hAB hAC hAD hBC hBD hCD hcover hA hC hsizeAB hsizeCD hnoAB hnoCD hdegree hsep
    x y hx hy Q W hQW hxQ hyQ hxW hyW hqe hwe (by rw [hcov]; exact hR)
    hyQadj hxWadj hQWadj
  apply boundary_five_blocks_defect_from_shore_shape k hk G A B C D
    hAB hAC hAD hBC hBD hCD hC hsizeCD hnoCD hdegree x y hx hy Q W hyQadj hxWadj hQWadj
  · exact hshape.1
  · intro ht
    obtain ⟨a,b,c⟩ := hshape.2 ht
    exact ⟨a,c⟩
