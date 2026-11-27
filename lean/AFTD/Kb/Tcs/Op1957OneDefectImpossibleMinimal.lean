import AFTD.Prelude
import AFTD.Kb.Tcs.BoundaryFiveOddBlocksOneDefectEssentialEdgeForcesTwo
import AFTD.Kb.Tcs.FourByFiveDefectIncidenceImpossible
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.IsKFactorCritical

/-!
# op1957_one_defect_impossible_minimal

Topic: graphs   Node: c80bc1b336fd

Provenance: helper lemma. OP-1957: five-by-odd boundary reduction, arXiv:2611.22690

Under the displayed five-by-odd block, degree, separator and minimality assumptions, every vertex of the five-vertex block has at least two nonneighbors in the opposite block.
-/

theorem op1957_one_defect_impossible_minimal
    (k c : ℕ) (hc : 7 ≤ c) (hcodd : Odd c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hB : B.card=2*k-5) (hC : C.card=c) (hD : D.card=2*k-c)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ a ∈ C, ∀ b ∈ D, ¬ G.Adj a b)
    (hcritB : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ X U V : Finset (Fin (4*k)), U.Nonempty → V.Nonempty →
      Disjoint X U → Disjoint X V → Disjoint U V → X ∪ U ∪ V = Finset.univ →
      (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v) → 2*k ≤ X.card)
    (hmin : is_minimally_k_extendable G k) :
    ∀ x ∈ A, 2 ≤ (C.filter (fun y => ¬ G.Adj x y)).card := by
  classical
  intro x hx
  by_contra hn
  have hdef : (C.filter (fun y => ¬ G.Adj x y)).card ≤ 1 := by omega
  let E := C.filter (fun y => G.Adj x y)
  have hsplit := Finset.card_filter_add_card_filter_not (s:=C) (fun y => G.Adj x y)
  have hE : 5 ≤ E.card := by dsimp [E]; omega
  obtain ⟨F,hFC,hFcard⟩ := Finset.exists_subset_card_eq hE
  apply four_by_five_defect_incidence_impossible (A.erase x) F (fun a y => ¬ G.Adj a y)
  · simp [Finset.card_erase_of_mem hx,hA]
  · exact hFcard
  · intro a ha
    have haA : a ∈ A := (Finset.mem_erase.mp ha).2
    have haB : a ∉ B := fun h => Finset.disjoint_left.mp hAB haA h
    have hbudget := anticomplete_neighbor_defect_bound G B a haB (hnoAB a haA)
      (2*k+4) 2 (by simp only [Fintype.card_fin]; omega) (by have := hdegree a; omega)
    apply le_trans (Finset.card_le_card ?_) hbudget
    intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hyE : y ∈ E := hFC hy'.1
    have hyC : y ∈ C := (Finset.mem_filter.mp hyE).1
    have hyB : y ∉ B := fun h => Finset.disjoint_left.mp hBC h hyC
    have hya : y ≠ a := fun h => Finset.disjoint_left.mp hAC haA (h ▸ hyC)
    simp only [Finset.mem_sdiff,Finset.mem_erase,Finset.mem_univ,true_and,SimpleGraph.mem_neighborFinset]
    exact ⟨⟨hya,hyB⟩,hy'.2⟩
  · intro y hy
    have hyE : y ∈ E := hFC hy
    have hyC : y ∈ C := (Finset.mem_filter.mp hyE).1
    have hxy : G.Adj x y := (Finset.mem_filter.mp hyE).2
    have he : ¬ is_k_extendable (G.deleteEdges {s(x,y)}) k := hmin.2 s(x,y) (by simpa using hxy)
    have hsizeAB : A.card+B.card=2*k := by omega
    have hsizeCD : C.card+D.card=2*k := by omega
    have hh := boundary_five_odd_blocks_one_defect_essential_edge_forces_two
      k c (by omega) hcodd hkc G A B C D hAB hAC hAD hBC hBD hCD hcover hA hC hsizeAB hsizeCD
      hnoAB hnoCD hcritB hdegree hsep hmin.1 x y hx hyC hxy he hdef
    have heq : (A.erase x).filter (fun a => ¬ G.Adj a y) = A.filter (fun a => ¬ G.Adj a y) := by
      ext a
      simp only [Finset.mem_filter,Finset.mem_erase]
      constructor
      · rintro ⟨⟨_,ha⟩,hn⟩; exact ⟨ha,hn⟩
      · rintro ⟨ha,hn⟩
        refine ⟨⟨?_,ha⟩,hn⟩
        intro h; subst a; exact hn hxy
    rw [heq]
    exact hh
