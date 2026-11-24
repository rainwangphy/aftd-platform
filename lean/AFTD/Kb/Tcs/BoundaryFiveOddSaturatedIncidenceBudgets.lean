import AFTD.Prelude
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound
import AFTD.Kb.Tcs.AnticompleteVertexFourDisjointNonneighborSetsBound
import AFTD.Kb.Tcs.FourBlockForbiddenShoreSeparatorBound

/-!
# boundary_five_odd_saturated_incidence_budgets

Topic: graphs   Node: 428f8874206e

Provenance: helper lemma. OP-1957, incidence-to-graph transfer

The displayed degree and separator hypotheses imply the row, column and forbidden-shore budgets required by the proved mixed-witness incidence theorem.
-/

set_option maxHeartbeats 4000000

theorem boundary_five_odd_saturated_incidence_budgets (k c : ℕ) (hc : 7 ≤ c) (hkc : c ≤ k) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj] (A B C D : Finset (Fin (4*k))) (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D) (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D) (hA : A.card=5) (hB : B.card=2*k-5) (hC : C.card=c) (hD : D.card=2*k-c) (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) (hnoCD : ∀ a ∈ C, ∀ b ∈ D, ¬ G.Adj a b) (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card) (hsep : ∀ X U V : Finset (Fin (4*k)), U.Nonempty → V.Nonempty → Disjoint X U → Disjoint X V → Disjoint U V → X ∪ U ∪ V = Finset.univ → (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v) → 2*k ≤ X.card) (x p q : Fin (4*k)) (hx : x ∈ A) (hp : p ∈ C) (hq : q ∈ C) (hxp : ¬ G.Adj x p) (hxq : ¬ G.Adj x q) : (∀ a ∈ A.erase x, (C.filter (fun y => ¬ G.Adj a y)).card ≤ 2) ∧ (∀ y ∈ C, ((A.erase x).filter (fun a => ¬ G.Adj a y)).card + (B.filter (fun b => ¬ G.Adj b y)).card + ((C.erase y).filter (fun z => ¬ G.Adj y z)).card + (if y=p ∨ y=q then 1 else 0) ≤ c-3) ∧ (∀ U ⊆ B, ∀ W ⊆ C, U.Nonempty → W.Nonempty → (∀ b ∈ U, ∀ z ∈ W, ¬ G.Adj b z) → U.card+W.card ≤ c) := by
  classical
  have k7 : 7 ≤ k := by omega
  constructor
  · intro a ha
    have haA : a ∈ A := (Finset.mem_erase.mp ha).2
    have haB : a ∉ B := fun hb => Finset.disjoint_left.mp hAB haA hb
    have hs : Fintype.card (Fin (4*k)) = B.card + (2*k+4) + 1 := by
      simp only [Fintype.card_fin]
      omega
    have hd : 2*k+4 ≤ (G.neighborFinset a).card + 2 := by
      have := hdegree a
      omega
    have hb := anticomplete_neighbor_defect_bound G B a haB (hnoAB a haA)
      (2*k+4) 2 hs hd
    apply le_trans (Finset.card_le_card ?_) hb
    intro y hy
    have hyC := (Finset.mem_filter.mp hy).1
    have hna := (Finset.mem_filter.mp hy).2
    have hyB : y ∉ B := fun hyB => Finset.disjoint_left.mp hBC hyB hyC
    have hya : y ≠ a := fun h => Finset.disjoint_left.mp hAC haA (h ▸ hyC)
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, true_and,
      SimpleGraph.mem_neighborFinset]
    exact ⟨⟨hya,hyB⟩,hna⟩
  constructor
  · intro y hy
    let S1 := (A.erase x).filter (fun a => ¬ G.Adj a y)
    let S2 := B.filter (fun b => ¬ G.Adj b y)
    let S3 := (C.erase y).filter (fun z => ¬ G.Adj y z)
    let S4 : Finset (Fin (4*k)) := if y=p ∨ y=q then {x} else ∅
    have s1A : S1 ⊆ A := fun _ h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).2
    have s2B : S2 ⊆ B := fun _ h => (Finset.mem_filter.mp h).1
    have s3C : S3 ⊆ C := fun _ h => (Finset.mem_erase.mp (Finset.mem_filter.mp h).1).2
    have s4A : S4 ⊆ A := by
      intro z hz
      dsimp [S4] at hz
      split at hz <;> simp_all
    have hyD : y ∉ D := fun h => Finset.disjoint_left.mp hCD hy h
    have hs : Fintype.card (Fin (4*k)) = D.card + (2*k+c-1) + 1 := by
      simp only [Fintype.card_fin]
      omega
    have hd : 2*k+c-1 ≤ (G.neighborFinset y).card + (c-3) := by
      have := hdegree y
      omega
    have hd12 : Disjoint S1 S2 := Finset.disjoint_of_subset_left s1A (Finset.disjoint_of_subset_right s2B hAB)
    have hd13 : Disjoint S1 S3 := Finset.disjoint_of_subset_left s1A (Finset.disjoint_of_subset_right s3C hAC)
    have hd23 : Disjoint S2 S3 := Finset.disjoint_of_subset_left s2B (Finset.disjoint_of_subset_right s3C hBC)
    have hd24 : Disjoint S2 S4 := Finset.disjoint_of_subset_left s2B (Finset.disjoint_of_subset_right s4A hAB.symm)
    have hd34 : Disjoint S3 S4 := Finset.disjoint_of_subset_left s3C (Finset.disjoint_of_subset_right s4A hAC.symm)
    have hd14 : Disjoint S1 S4 := by
      apply Finset.disjoint_left.mpr
      intro z hz1 hz4
      have hz1' := (Finset.mem_erase.mp (Finset.mem_filter.mp hz1).1).1
      dsimp [S4] at hz4
      split at hz4 <;> simp_all
    have hnon : ∀ w, (w ∈ S1 ∨ w ∈ S2 ∨ w ∈ S3 ∨ w ∈ S4) → w ≠ y ∧ ¬ G.Adj y w := by
      intro w hw
      rcases hw with hw | hw | hw | hw
      · have hwA := s1A hw
        have hwy : w ≠ y := fun h => Finset.disjoint_left.mp hAC hwA (h ▸ hy)
        exact ⟨hwy, fun h => (Finset.mem_filter.mp hw).2 h.symm⟩
      · have hwB := s2B hw
        have hwy : w ≠ y := fun h => Finset.disjoint_left.mp hBC hwB (h ▸ hy)
        exact ⟨hwy, fun h => (Finset.mem_filter.mp hw).2 h.symm⟩
      · exact ⟨(Finset.mem_erase.mp (Finset.mem_filter.mp hw).1).1, (Finset.mem_filter.mp hw).2⟩
      · have hwA := s4A hw
        have hwy : w ≠ y := fun h => Finset.disjoint_left.mp hAC hwA (h ▸ hy)
        have heq : w = x := by
          dsimp [S4] at hw
          split at hw <;> simp_all
        have hycase : y=p ∨ y=q := by
          dsimp [S4] at hw
          split at hw <;> simp_all
        subst w
        exact ⟨hwy, fun h => hycase.elim (fun h' => hxp (h' ▸ h.symm)) (fun h' => hxq (h' ▸ h.symm))⟩
    have hb := anticomplete_vertex_four_disjoint_nonneighbor_sets_bound G D y hyD
      (hnoCD y hy) (2*k+c-1) (c-3) hs hd S1 S2 S3 S4 hnon hd12 hd13 hd14 hd23 hd24 hd34
    have hs1D : Disjoint S1 D := Finset.disjoint_of_subset_left s1A hAD
    have hs2D : Disjoint S2 D := Finset.disjoint_of_subset_left s2B hBD
    have hs3D : Disjoint S3 D := Finset.disjoint_of_subset_left s3C hCD
    have hs4D : Disjoint S4 D := Finset.disjoint_of_subset_left s4A hAD
    rw [Finset.sdiff_eq_self_of_disjoint hs1D, Finset.sdiff_eq_self_of_disjoint hs2D,
      Finset.sdiff_eq_self_of_disjoint hs3D, Finset.sdiff_eq_self_of_disjoint hs4D] at hb
    by_cases h : y=p ∨ y=q <;> simpa [S1,S2,S3,S4,h] using hb
  · intro U hUB W hWC hUne hWne hUW
    let P := D ∪ U
    let X := Finset.univ \ (P ∪ W)
    have hDne : D.Nonempty := Finset.card_pos.mp (by omega)
    have hPne : P.Nonempty := hDne.mono (Finset.subset_union_left)
    have hPW : Disjoint P W := by
      apply Finset.disjoint_left.mpr
      intro z hzP hzW
      rcases Finset.mem_union.mp hzP with hzD | hzU
      · exact Finset.disjoint_left.mp hCD (hWC hzW) hzD
      · exact Finset.disjoint_left.mp hBC (hUB hzU) (hWC hzW)
    have hXP : Disjoint X P := by
      apply Finset.disjoint_left.mpr
      intro z hzX hzP
      exact (Finset.mem_sdiff.mp hzX).2 (Finset.mem_union_left _ hzP)
    have hXW : Disjoint X W := by
      apply Finset.disjoint_left.mpr
      intro z hzX hzW
      exact (Finset.mem_sdiff.mp hzX).2 (Finset.mem_union_right _ hzW)
    have hcover : X ∪ P ∪ W = Finset.univ := by ext z; simp [X]
    have hanti : ∀ a ∈ P, ∀ b ∈ W, ¬ G.Adj a b := by
      intro a ha b hb hab
      rcases Finset.mem_union.mp ha with haD | haU
      · exact hnoCD b (hWC hb) a haD hab.symm
      · exact hUW a haU b hb hab
    have hcut := hsep X P W hPne hWne hXP hXW hPW hcover hanti
    have hDU : Disjoint D U := Finset.disjoint_of_subset_right hUB hBD.symm
    have hPcard : P.card = D.card + U.card := Finset.card_union_of_disjoint hDU
    have hPWcard : (P ∪ W).card = P.card + W.card := Finset.card_union_of_disjoint hPW
    have htotal := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin (4*k))) (P ∪ W)
    simp only [Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at htotal
    change X.card + (P ∪ W).card = 4*k at htotal
    rw [hPWcard,hPcard] at htotal
    omega
