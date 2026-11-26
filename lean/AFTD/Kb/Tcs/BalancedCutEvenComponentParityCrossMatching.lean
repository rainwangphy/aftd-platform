import AFTD.Prelude
import AFTD.Kb.Tcs.BalancedCutEvenlyDistributedCrossMatchingSharp
import AFTD.Kb.Tcs.BalancedCutAnticompleteSideHasCrossMatching

/-!
# balanced_cut_even_component_parity_cross_matching

Topic: graphs   Node: 5974a5ca390b

Provenance: helper lemma. Balanced-cut parity reduction for OP-1957; https://arxiv.org/abs/2611.22690.

In the stated separator setting, an even number of crossing endpoints may be chosen in each specified odd-side group by sending one extra crossing edge into a disjoint component.
-/

theorem balanced_cut_even_component_parity_cross_matching
    (k n : ℕ) (hn : Even n) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (C U H : Finset (Fin (4*k))) (hcard : C.card = 2*k) (hUC : U ⊆ C)
    (hU : 2*(n+1) ≤ U.card) (hCH : Disjoint C H) (hH : H.Nonempty)
    (hHanti : ∀ u ∈ H, ∀ v, v ∉ C → v ∉ H → ¬ G.Adj u v)
    {I : Type*} [DecidableEq I] (J : Finset I) (F : I → Finset (Fin (4*k)))
    (hJ : n+2 ≤ J.card)
    (hCF : ∀ i ∈ J, Disjoint C (F i))
    (hHF : ∀ i ∈ J, Disjoint H (F i))
    (hdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (F i) (F j))
    (hsize : ∀ i ∈ J, 2 ≤ (F i).card)
    (hanti : ∀ i ∈ J, ∀ u ∈ F i, ∀ v, v ∉ C → v ∉ F i → ¬ G.Adj u v) :
    ∃ f g : Fin (n+1) → Fin (4*k), Function.Injective f ∧ Function.Injective g ∧
      (∀ a, f a ∈ U ∧ g a ∉ C ∧ G.Adj (f a) (g a)) ∧
      (∀ i ∈ J, Even (((Finset.univ : Finset (Fin (n+1))).image g) ∩ F i).card) := by
  set_option maxHeartbeats 4000000 in
    classical
    obtain ⟨f0,g0,hf0,hg0,hfg0⟩ :=
      balanced_cut_anticomplete_side_has_cross_matching k 1 (by omega) G hsep C H U
        hcard hCH hUC hHanti (by omega) (Finset.one_le_card.mpr hH)
    let A : Finset (Fin (4*k)) := (Finset.univ : Finset (Fin 1)).image f0
    let U' := U \ A
    have hA : A.card = 1 := by
      dsimp [A]
      rw [Finset.card_image_of_injective _ hf0]
      simp
    have hUC' : U' ⊆ C := (Finset.sdiff_subset : U' ⊆ U).trans hUC
    have hU' : 2*n ≤ U'.card := by
      have hh := Finset.card_sdiff_add_card_inter U A
      have hh' : (U ∩ A).card ≤ A.card := Finset.card_le_card Finset.inter_subset_right
      dsimp [U']
      omega
    obtain ⟨f,g,hf,hg,hfg,hgroups,B,hB,hpar⟩ :=
      balanced_cut_evenly_distributed_cross_matching_sharp k n G hsep C U' hcard hUC' hU' J F hJ hCF hdis hsize hanti
    have hBempty : B = ∅ := by
      rw [Nat.even_iff] at hn
      have hc : B.card = 0 := by omega
      exact Finset.card_eq_zero.mp hc
    have hfd : ∀ a b, f a ≠ f0 b := by
      intro a b he
      have ha := (Finset.mem_sdiff.mp (hfg a).1).2
      apply ha
      dsimp [A]
      exact Finset.mem_image.mpr ⟨b,Finset.mem_univ _,he.symm⟩
    have hgnot : ∀ a, g a ∉ H := by
      intro a ha
      obtain ⟨i,hi,hgi⟩ := hgroups a
      exact Finset.disjoint_left.mp (hHF i hi) ha hgi
    have hgd : ∀ a b, g a ≠ g0 b := by
      intro a b he
      exact hgnot a (he.symm ▸ (hfg0 b).2.1)
    let ff := Fin.append f f0
    let gg := Fin.append g g0
    have hff : Function.Injective ff := Fin.append_injective_iff.mpr ⟨hf,hf0,hfd⟩
    have hgg : Function.Injective gg := Fin.append_injective_iff.mpr ⟨hg,hg0,hgd⟩
    have hboth : ∀ a, ff a ∈ U ∧ gg a ∉ C ∧ G.Adj (ff a) (gg a) := by
      intro a
      refine Fin.addCases ?_ ?_ a
      · intro b
        obtain ⟨i,hi,hgi⟩ := hgroups b
        have hnC : g b ∉ C := fun h => Finset.disjoint_left.mp (hCF i hi) h hgi
        simpa [ff,gg] using ⟨(Finset.mem_sdiff.mp (hfg b).1).1,hnC,(hfg b).2⟩
      · intro b
        have hnC : g0 b ∉ C := fun h => Finset.disjoint_left.mp hCH h (hfg0 b).2.1
        simpa [ff,gg] using ⟨(hfg0 b).1,hnC,(hfg0 b).2.2⟩
    have himage : ((Finset.univ : Finset (Fin (n+1))).image gg) =
        ((Finset.univ : Finset (Fin n)).image g) ∪ ((Finset.univ : Finset (Fin 1)).image g0) := by
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
        · exact ⟨Fin.castAdd 1 b,by simpa [gg] using hb⟩
        · exact ⟨Fin.natAdd n b,by simpa [gg] using hb⟩
    refine ⟨ff,gg,hff,hgg,hboth,?_⟩
    intro i hi
    rw [himage]
    have hzero : Disjoint ((Finset.univ : Finset (Fin 1)).image g0) (F i) := by
      apply Finset.disjoint_left.mpr
      intro v hvg hvi
      obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hvg
      exact Finset.disjoint_left.mp (hHF i hi) (hfg0 a).2.1 hvi
    have heq : (((Finset.univ : Finset (Fin n)).image g) ∪
        ((Finset.univ : Finset (Fin 1)).image g0)) ∩ F i =
          ((Finset.univ : Finset (Fin n)).image g) ∩ F i := by
      ext v
      simp only [Finset.mem_inter,Finset.mem_union]
      constructor
      · rintro ⟨hv | hv,hvi⟩
        · exact ⟨hv,hvi⟩
        · exact False.elim (Finset.disjoint_left.mp hzero hv hvi)
      · rintro ⟨hv,hvi⟩
        exact ⟨Or.inl hv,hvi⟩
    rw [heq]
    exact hpar i hi (by simp [hBempty])
