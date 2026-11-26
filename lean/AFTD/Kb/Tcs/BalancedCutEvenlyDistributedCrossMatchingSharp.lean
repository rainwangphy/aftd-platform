import AFTD.Prelude
import AFTD.Kb.Tcs.BalancedCutAnticompleteSideHasCrossMatching

/-!
# balanced_cut_evenly_distributed_cross_matching_sharp

Topic: graphs   Node: e717de8c3809

Provenance: helper lemma. Balanced-cut parity reduction for OP-1957; https://arxiv.org/abs/2611.22690.

The stated separator condition supplies r crossing edges whose far endpoints meet an odd number of vertices in at most r mod 2 groups.
-/

theorem balanced_cut_evenly_distributed_cross_matching_sharp
    (k r : ℕ) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (C U : Finset (Fin (4*k))) (hcard : C.card = 2*k) (hUC : U ⊆ C)
    (hU : 2*r ≤ U.card) {I : Type*} [DecidableEq I]
    (J : Finset I) (F : I → Finset (Fin (4*k))) (hJ : r+2 ≤ J.card)
    (hCH : ∀ i ∈ J, Disjoint C (F i))
    (hdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (F i) (F j))
    (hsize : ∀ i ∈ J, 2 ≤ (F i).card)
    (hanti : ∀ i ∈ J, ∀ u ∈ F i, ∀ v, v ∉ C → v ∉ F i → ¬ G.Adj u v) :
    ∃ f g : Fin r → Fin (4*k), Function.Injective f ∧ Function.Injective g ∧
      (∀ a, f a ∈ U ∧ G.Adj (f a) (g a)) ∧
      (∀ a, ∃ i ∈ J, g a ∈ F i) ∧
      ∃ B : Finset I, B.card ≤ r % 2 ∧
        ∀ i ∈ J, i ∉ B → Even (((Finset.univ : Finset (Fin r)).image g) ∩ F i).card := by
  set_option maxHeartbeats 4000000 in
    classical
    revert U J
    induction r using Nat.twoStepInduction with
    | zero =>
      intro U hUC hU J hJ hCH hdis hsize hanti
      refine ⟨Fin.elim0,Fin.elim0,?_,?_,?_,?_,∅,by simp,?_⟩
      · intro x
        exact Fin.elim0 x
      · intro x
        exact Fin.elim0 x
      · intro x
        exact Fin.elim0 x
      · intro x
        exact Fin.elim0 x
      · intro i hi _
        simp
    | one =>
      intro U hUC hU J hJ hCH hdis hsize hanti
      obtain ⟨j,hj⟩ := Finset.card_pos.mp (by omega : 0 < J.card)
      obtain ⟨f,g,hf,hg,hfg⟩ :=
        balanced_cut_anticomplete_side_has_cross_matching k 1 (by omega) G hsep C (F j) U
          hcard (hCH j hj) hUC (hanti j hj) (by omega) (by have := hsize j hj; omega)
      refine ⟨f,g,hf,hg,(fun a => ⟨(hfg a).1,(hfg a).2.2⟩),?_,{j},by simp,?_⟩
      · intro a
        exact ⟨j,hj,(hfg a).2.1⟩
      · intro i hi hiB
        have hij : i ≠ j := by simpa using hiB
        have hnull : ((Finset.univ : Finset (Fin 1)).image g) ∩ F i = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro v hv
          obtain ⟨hvg,hvi⟩ := Finset.mem_inter.mp hv
          obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hvg
          exact Finset.disjoint_left.mp (hdis i hi j hj hij) hvi (hfg a).2.1
        rw [hnull]
        simp
    | more r ih _ =>
      intro U hUC hU J hJ hCH hdis hsize hanti
      obtain ⟨j,hj⟩ := Finset.card_pos.mp (by omega : 0 < J.card)
      obtain ⟨f0,g0,hf0,hg0,hfg0⟩ :=
        balanced_cut_anticomplete_side_has_cross_matching k 2 (by omega) G hsep C (F j) U
          hcard (hCH j hj) hUC (hanti j hj) (by omega) (hsize j hj)
      let A : Finset (Fin (4*k)) := (Finset.univ : Finset (Fin 2)).image f0
      let U' : Finset (Fin (4*k)) := U \ A
      let J' : Finset I := J.erase j
      have hAcard : A.card = 2 := by
        dsimp [A]
        rw [Finset.card_image_of_injective _ hf0]
        simp
      have hUC' : U' ⊆ C := (Finset.sdiff_subset : U' ⊆ U).trans hUC
      have hU' : 2*r ≤ U'.card := by
        have hh := Finset.card_sdiff_add_card_inter U A
        have hh' : (U ∩ A).card ≤ A.card := Finset.card_le_card Finset.inter_subset_right
        dsimp [U']
        omega
      have hJ' : r+2 ≤ J'.card := by
        have hh := Finset.card_erase_add_one hj
        dsimp [J']
        omega
      have hCH' : ∀ i ∈ J', Disjoint C (F i) := by
        intro i hi
        exact hCH i (Finset.mem_erase.mp hi).2
      have hdis' : ∀ i ∈ J', ∀ l ∈ J', i ≠ l → Disjoint (F i) (F l) := by
        intro i hi l hl hil
        exact hdis i (Finset.mem_erase.mp hi).2 l (Finset.mem_erase.mp hl).2 hil
      have hsize' : ∀ i ∈ J', 2 ≤ (F i).card := by
        intro i hi
        exact hsize i (Finset.mem_erase.mp hi).2
      have hanti' : ∀ i ∈ J', ∀ u ∈ F i, ∀ v, v ∉ C → v ∉ F i → ¬ G.Adj u v := by
        intro i hi
        exact hanti i (Finset.mem_erase.mp hi).2
      obtain ⟨f,g,hf,hg,hfg,hgroups,B,hB,hpar⟩ :=
        ih U' hUC' hU' J' hJ' hCH' hdis' hsize' hanti'
      have hfd : ∀ a b, f a ≠ f0 b := by
        intro a b he
        have hn := (Finset.mem_sdiff.mp (hfg a).1).2
        apply hn
        dsimp [A]
        exact Finset.mem_image.mpr ⟨b,Finset.mem_univ _,he.symm⟩
      have hgnot : ∀ a, g a ∉ F j := by
        intro a hgj
        obtain ⟨i,hi,hgi⟩ := hgroups a
        have hne : i ≠ j := (Finset.mem_erase.mp hi).1
        exact Finset.disjoint_left.mp (hdis i (Finset.mem_erase.mp hi).2 j hj hne) hgi hgj
      have hgd : ∀ a b, g a ≠ g0 b := by
        intro a b he
        exact hgnot a (he.symm ▸ (hfg0 b).2.1)
      let ff := Fin.append f f0
      let gg := Fin.append g g0
      have hff : Function.Injective ff := Fin.append_injective_iff.mpr ⟨hf,hf0,hfd⟩
      have hgg : Function.Injective gg := Fin.append_injective_iff.mpr ⟨hg,hg0,hgd⟩
      have hboth : ∀ a, ff a ∈ U ∧ G.Adj (ff a) (gg a) := by
        intro a
        refine Fin.addCases ?_ ?_ a
        · intro b
          simpa [ff,gg] using ⟨(Finset.mem_sdiff.mp (hfg b).1).1,(hfg b).2⟩
        · intro b
          simpa [ff,gg] using ⟨(hfg0 b).1,(hfg0 b).2.2⟩
      have hwhere : ∀ a, ∃ i ∈ J, gg a ∈ F i := by
        intro a
        refine Fin.addCases ?_ ?_ a
        · intro b
          obtain ⟨i,hi,hgi⟩ := hgroups b
          exact ⟨i,(Finset.mem_erase.mp hi).2,by simpa [gg] using hgi⟩
        · intro b
          exact ⟨j,hj,by simpa [gg] using (hfg0 b).2.1⟩
      have himage : ((Finset.univ : Finset (Fin (r+2))).image gg) =
          ((Finset.univ : Finset (Fin r)).image g) ∪ ((Finset.univ : Finset (Fin 2)).image g0) := by
        ext v
        simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_union]
        constructor
        · rintro ⟨a,ha⟩
          cases a using Fin.addCases with
          | left b =>
            left
            exact ⟨b,by simpa [gg] using ha⟩
          | right b =>
            right
            exact ⟨b,by simpa [gg] using ha⟩
        · rintro (⟨b,hb⟩ | ⟨b,hb⟩)
          · exact ⟨Fin.castAdd 2 b,by simpa [gg] using hb⟩
          · exact ⟨Fin.natAdd r b,by simpa [gg] using hb⟩
      refine ⟨ff,gg,hff,hgg,hboth,hwhere,B,?_,?_⟩
      · omega
      intro i hi hiB
      rw [himage]
      by_cases hij : i = j
      · subst i
        have hzero : Disjoint ((Finset.univ : Finset (Fin r)).image g) (F j) := by
          apply Finset.disjoint_left.mpr
          intro v hvg hvj
          obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hvg
          exact hgnot a hvj
        have hsub : ((Finset.univ : Finset (Fin 2)).image g0) ⊆ F j := by
          intro v hv
          obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hv
          exact (hfg0 a).2.1
        have heq : (((Finset.univ : Finset (Fin r)).image g) ∪
            ((Finset.univ : Finset (Fin 2)).image g0)) ∩ F j =
              ((Finset.univ : Finset (Fin 2)).image g0) := by
          ext v
          simp only [Finset.mem_inter,Finset.mem_union]
          constructor
          · rintro ⟨hv | hv,hvj⟩
            · exact False.elim (Finset.disjoint_left.mp hzero hv hvj)
            · exact hv
          · intro hv
            exact ⟨Or.inr hv,hsub hv⟩
        rw [heq,Finset.card_image_of_injective _ hg0]
        simp
      · have hi' : i ∈ J' := Finset.mem_erase.mpr ⟨hij,hi⟩
        have hzero : Disjoint ((Finset.univ : Finset (Fin 2)).image g0) (F i) := by
          apply Finset.disjoint_left.mpr
          intro v hvg hvi
          obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hvg
          exact Finset.disjoint_left.mp (hdis i hi j hj hij) hvi (hfg0 a).2.1
        have heq : (((Finset.univ : Finset (Fin r)).image g) ∪
            ((Finset.univ : Finset (Fin 2)).image g0)) ∩ F i =
              ((Finset.univ : Finset (Fin r)).image g) ∩ F i := by
          ext v
          simp only [Finset.mem_inter,Finset.mem_union]
          constructor
          · rintro ⟨hv | hv,hvi⟩
            · exact ⟨hv,hvi⟩
            · exact False.elim (Finset.disjoint_left.mp hzero hv hvi)
          · rintro ⟨hv,hvi⟩
            exact ⟨Or.inl hv,hvi⟩
        rw [heq]
        exact hpar i hi' hiB
