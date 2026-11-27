import AFTD.Prelude
import AFTD.Kb.Tcs.IsMinimallyKExtendable
import AFTD.Kb.Tcs.IsKFactorCritical
import AFTD.Kb.Tcs.BoundaryFiveOddBlocksOneDefectEssentialEdgeForcesTwo
import AFTD.Kb.Tcs.FourByFiveDefectIncidenceImpossible
import AFTD.Kb.Tcs.Op1957OneDefectImpossibleMinimal
import AFTD.Kb.Tcs.BoundaryFiveOddSaturatedTwoDefectMinimalContradiction
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound

/-!
# minimally_k_extendable_five_odd_block_degree_bound_with_separator

Topic: graphs   Node: 1ad5da28d861

Provenance: original. Related work: OP-1957: conditional five-by-arbitrary-odd-block boundary degree route.

For every odd natural number c at least seven and every k at least c, let G be a connected minimally k-extendible graph on 4k vertices, with decidable adjacency. Suppose the vertices partition into pairwise disjoint sets A, B, C, D of sizes 5, 2k−5, c and 2k−c respectively, with A anticomplete to B, C anticomplete to D, and the induced B-block graph 1-factor-critical. Assume that every partition into pairwise disjoint sets X, U, V covering all vertices, with U and V nonempty and anticomplete, has |X| at least 2k. Then G has a vertex of degree at most 2k+1.
-/

theorem minimally_k_extendable_five_odd_block_degree_bound_with_separator
    (k c : ℕ) (hc : 7 ≤ c) (hcodd : Odd c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : is_minimally_k_extendable G k)
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hB : B.card=2*k-5) (hC : C.card=c) (hD : D.card=2*k-c)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hcritB : is_k_factor_critical (G.induce {v | v ∈ B}) 1)
    (hsep : ∀ X U V : Finset (Fin (4*k)), U.Nonempty → V.Nonempty →
      Disjoint X U → Disjoint X V → Disjoint U V → X ∪ U ∪ V = Finset.univ →
      (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v) → 2*k ≤ X.card) :
    ∃ v, (G.neighborFinset v).card ≤ 2*k+1 := by
  classical
  by_contra hnone
  push_neg at hnone
  have hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card := by
    intro v
    have hh := hnone v
    omega
  have hAlarge : A.Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨x,hx⟩ := hAlarge
  let P := C.filter (fun y => ¬ G.Adj x y)
  let Q := ((Finset.univ \ B).erase x) \ G.neighborFinset x
  have hxB : x ∉ B := fun h => Finset.disjoint_left.mp hAB hx h
  have hbudget : Q.card ≤ 2 := anticomplete_neighbor_defect_bound G B x hxB (hnoAB x hx)
    (2*k+4) 2 (by simp only [Fintype.card_fin]; omega) (by have := hdegree x; omega)
  have hPsub : P ⊆ Q := by
    intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hyB : y ∉ B := fun h => Finset.disjoint_left.mp hBC h hy'.1
    have hyx : y ≠ x := fun h => Finset.disjoint_left.mp hAC hx (h ▸ hy'.1)
    simp only [Q,Finset.mem_sdiff,Finset.mem_erase,Finset.mem_univ,true_and,SimpleGraph.mem_neighborFinset]
    exact ⟨⟨hyx,hyB⟩,hy'.2⟩
  have hlower := op1957_one_defect_impossible_minimal k c hc hcodd hkc G A B C D
    hAB hAC hAD hBC hBD hCD hcover hA hB hC hD hnoAB hnoCD hcritB hdegree hsep hmin x hx
  have hPcard : P.card=2 := by
    have hh := Finset.card_le_card hPsub
    change 2 ≤ P.card at hlower
    omega
  have hPQ : P=Q := Finset.eq_of_subset_of_card_le hPsub (by omega)
  obtain ⟨p,q,hpq,hP⟩ := Finset.card_eq_two.mp hPcard
  have hpP : p ∈ P := by rw [hP]; simp
  have hqP : q ∈ P := by rw [hP]; simp
  have hpC : p ∈ C := (Finset.mem_filter.mp hpP).1
  have hqC : q ∈ C := (Finset.mem_filter.mp hqP).1
  have hxp : ¬ G.Adj x p := (Finset.mem_filter.mp hpP).2
  have hxq : ¬ G.Adj x q := (Finset.mem_filter.mp hqP).2
  have hfull : ∀ y ∈ C, y ≠ p → y ≠ q → G.Adj x y := by
    intro y hy hyp hyq
    by_contra h
    have hyP : y ∈ P := Finset.mem_filter.mpr ⟨hy,h⟩
    rw [hP] at hyP
    simp [hyp,hyq] at hyP
  have hsatA : ∀ a ∈ A, a ≠ x → G.Adj x a := by
    intro a ha hax
    by_contra h
    have haB : a ∉ B := fun hb => Finset.disjoint_left.mp hAB ha hb
    have haQ : a ∈ Q := by
      simp only [Q,Finset.mem_sdiff,Finset.mem_erase,Finset.mem_univ,true_and,SimpleGraph.mem_neighborFinset]
      exact ⟨⟨hax,haB⟩,h⟩
    have haP : a ∈ P := by rw [hPQ]; exact haQ
    have haC := (Finset.mem_filter.mp haP).1
    exact Finset.disjoint_left.mp hAC ha haC
  have hsatD : ∀ d ∈ D, G.Adj x d := by
    intro d hd
    by_contra h
    have hdB : d ∉ B := fun hb => Finset.disjoint_left.mp hBD hb hd
    have hdx : d ≠ x := fun he => Finset.disjoint_left.mp hAD hx (he ▸ hd)
    have hdQ : d ∈ Q := by
      simp only [Q,Finset.mem_sdiff,Finset.mem_erase,Finset.mem_univ,true_and,SimpleGraph.mem_neighborFinset]
      exact ⟨⟨hdx,hdB⟩,h⟩
    have hdP : d ∈ P := by rw [hPQ]; exact hdQ
    have hdC := (Finset.mem_filter.mp hdP).1
    exact Finset.disjoint_left.mp hCD hdC hd
  exact boundary_five_odd_saturated_two_defect_minimal_contradiction k c hc hcodd hkc G A B C D
    hAB hAC hAD hBC hBD hCD hcover hA hB hC hD hnoAB hnoCD hcritB hdegree hsep hmin
    x p q hx hpC hqC hpq hxp hxq hfull hsatA hsatD
