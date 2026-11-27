import AFTD.Prelude
import AFTD.Kb.Tcs.BoundarySaturatedBlockFactorcriticalOppositeCrossRemovable
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.IsKExtendable

/-!
# minimally_k_extendable_triangle_component_boundary_degree_bound_with_separator

Topic: graphs   Node: 31a545b4d328

Provenance: helper lemma. OP-1957: saturated-block boundary reduction, arXiv:2611.22690 and arXiv:1011.3384

For a minimally k-extendible graph with the displayed four-block partition, a three-vertex block, a factor-critical opposite same-side block and the 2k-separator property, some vertex has degree at most 2k+1.
-/

theorem minimally_k_extendable_triangle_component_boundary_degree_bound_with_separator
    (k : ℕ) (hk : 4 ≤ k) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hmin : is_minimally_k_extendable G k)
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hsizeAB : A.card+B.card=2*k) (hsizeCD : C.card+D.card=2*k)
    (hA : A.card=3) (hCmin : 3 ≤ C.card) (hC : C.card ≤ k)
    (hBcrit : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hsep : ∀ X U V : Finset (Fin (4*k)), U.Nonempty → V.Nonempty →
      Disjoint X U → Disjoint X V → Disjoint U V → X ∪ U ∪ V = Finset.univ →
      (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v) → 2*k ≤ X.card) :
    ∃ v, (G.neighborFinset v).card ≤ 2*k+1 := by
  classical
  by_contra hnone
  push Not at hnone
  have hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card := by
    intro v
    have hh := hnone v
    omega
  have hAsat : ∀ a ∈ A, ∀ w ∈ A ∪ C ∪ D, a ≠ w → G.Adj a w := by
    intro a ha w hw haw
    have haB : a ∉ B := fun h => Finset.disjoint_left.mp hAB ha h
    have hbudget := anticomplete_neighbor_defect_bound G B a haB (hnoAB a ha)
      (2*k+2) 0 (by simp only [Fintype.card_fin]; omega) (by have := hdegree a; omega)
    have hwB : w ∉ B := by
      intro hb
      simp only [Finset.mem_union] at hw
      rcases hw with (hwA | hwC) | hwD
      · exact Finset.disjoint_left.mp hAB hwA hb
      · exact Finset.disjoint_left.mp hBC hb hwC
      · exact Finset.disjoint_left.mp hBD hb hwD
    by_contra hn
    have hwQ : w ∈ (((Finset.univ \ B).erase a) \ G.neighborFinset a) := by
      simp only [Finset.mem_sdiff,Finset.mem_erase,Finset.mem_univ,true_and,SimpleGraph.mem_neighborFinset]
      exact ⟨⟨haw.symm,hwB⟩,hn⟩
    have hp := Finset.card_pos.mpr ⟨w,hwQ⟩
    omega
  obtain ⟨x,hx⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨y,hy⟩ : C.Nonempty := Finset.card_pos.mp (by omega)
  have hxyne : x ≠ y := fun h => Finset.disjoint_left.mp hAC hx (h ▸ hy)
  have hxy := hAsat x hx y (Finset.mem_union_left _ (Finset.mem_union_right _ hy)) hxyne
  have hrem := boundary_saturated_block_factorcritical_opposite_cross_removable k hk G A B C D
    hAB hAC hAD hBC hBD hCD hcover hsizeAB hsizeCD (by omega) hC hnoAB hnoCD hAsat
    hdegree hsep hBcrit hmin.1 x y hx hy hxy
  exact hmin.2 s(x,y) (by simpa using hxy) hrem
