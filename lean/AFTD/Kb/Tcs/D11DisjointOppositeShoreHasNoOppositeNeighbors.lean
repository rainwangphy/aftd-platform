import AFTD.Prelude

/-!
# d11_disjoint_opposite_shore_has_no_opposite_neighbors

Topic: graphs   Node: 8a5f93bb8da9

Provenance: helper lemma. OP-1957 factor-critical saturated-twin d=11 case; scratch Lean axiom audit completed.

The displayed d=11 nested-shore pattern contradicts the complement degree bound.
-/

theorem d11_disjoint_opposite_shore_has_no_opposite_neighbors
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (S C A B : Finset V) (Q W : V → Finset V) (z₀ e : V)
    (hSC : Disjoint S C) (hS : S.card=10) (hA : A ⊆ S) (hAcard : A.card=4)
    (hE : 6 ≤ (B ∩ C).card) (hz₀ : z₀ ∈ C) (hQ₀ : Q z₀ = B) (he : e ∈ B ∩ C)
    (hmax : ∀ v, (H.neighborFinset v).card ≤ 11)
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=12)
    (havoid : ∀ z ∈ C, Disjoint A (Q z))
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hBA : ∀ e ∈ B ∩ C, ∀ a ∈ A, H.Adj e a)
    (hWe : W e = S \ A) :
    ∀ q ∈ B ∩ C, ¬ H.Adj e q := by
  classical
  let D := S \ A
  have hDsize : D.card=6 := by
    have hc := Finset.card_sdiff_add_card_eq_card hA
    dsimp [D]
    omega
  have hDC : Disjoint D C := by
    apply Finset.disjoint_left.mpr
    intro a ha hc
    exact (Finset.disjoint_left.mp hSC) (Finset.mem_sdiff.mp ha).1 hc
  have hrootnotB : z₀ ∉ B := by
    intro hzB
    have hzQ0 : z₀ ∈ Q z₀ := hQ₀.symm ▸ hzB
    exact (hzQ z₀ hz₀ z₀ hzQ0).ne rfl
  have heC : e ∈ C := (Finset.mem_inter.mp he).2
  have heB : e ∈ B := (Finset.mem_inter.mp he).1
  have heroot : e ≠ z₀ := fun h => hrootnotB (h ▸ heB)
  have hrootedge : H.Adj e z₀ := (hzQ z₀ hz₀ e (hQ₀.symm ▸ heB)).symm
  have hEsub : B ∩ C ⊆ H.neighborFinset z₀ := by
    intro q hq
    exact (H.mem_neighborFinset z₀ q).mpr (hzQ z₀ hz₀ q (hQ₀.symm ▸ (Finset.mem_inter.mp hq).1))
  have hQeC : Q e ⊆ C := by
    intro q hq
    rcases Finset.mem_union.mp (hQ e heC hq) with hqS | hqC
    · by_cases hqA : q ∈ A
      · exact ((Finset.disjoint_left.mp (havoid e heC)) hqA hq).elim
      · have hqD : q ∈ D := Finset.mem_sdiff.mpr ⟨hqS,hqA⟩
        have hqW : q ∈ W e := hWe.symm ▸ hqD
        exact ((Finset.disjoint_left.mp (hdis e heC)) hq hqW).elim
    · exact hqC
  have hQesize : (Q e).card=6 := by
    have hs := hsize e heC
    rw [hWe] at hs
    change (Q e).card + D.card = 12 at hs
    omega
  have hrootnotQ : z₀ ∉ Q e := by
    intro hzQe
    have hDsub : D ⊆ H.neighborFinset z₀ := by
      intro a ha
      exact (H.mem_neighborFinset z₀ a).mpr (hcross e heC z₀ hzQe a (hWe.symm ▸ ha))
    have hd : Disjoint D (B ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hDC) ha (Finset.mem_inter.mp hb).2
    have hc := Finset.card_le_card (Finset.union_subset hDsub hEsub)
    rw [Finset.card_union_of_disjoint hd,hDsize] at hc
    have hm := hmax z₀
    omega
  have hQeE : Disjoint (Q e) (B ∩ C) := by
    apply Finset.disjoint_left.mpr
    intro q hqQ hqE
    have hqS : S ⊆ H.neighborFinset q := by
      intro s hs
      by_cases hsA : s ∈ A
      · exact (H.mem_neighborFinset q s).mpr (hBA q hqE s hsA)
      · have hsD : s ∈ D := Finset.mem_sdiff.mpr ⟨hs,hsA⟩
        exact (H.mem_neighborFinset q s).mpr (hcross e heC q hqQ s (hWe.symm ▸ hsD))
    have heS : e ∉ S := fun h => (Finset.disjoint_left.mp hSC) h heC
    have hrS : z₀ ∉ S := fun h => (Finset.disjoint_left.mp hSC) h hz₀
    have henot : e ∉ insert z₀ S := by simp [heroot,heS]
    have hqe : H.Adj q e := (hzQ e heC q hqQ).symm
    have hqr : H.Adj q z₀ := (hzQ z₀ hz₀ q (hQ₀.symm ▸ (Finset.mem_inter.mp hqE).1)).symm
    have hsub : insert e (insert z₀ S) ⊆ H.neighborFinset q := by
      intro v hv
      simp only [Finset.mem_insert] at hv
      rcases hv with rfl | rfl | hv
      · simpa using hqe
      · simpa using hqr
      · exact hqS hv
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem henot,Finset.card_insert_of_notMem hrS,hS] at hc
    have hm := hmax q
    omega
  intro q hqE heq
  have hAQ : Disjoint A (Q e) := havoid e heC
  have hrootA : z₀ ∉ A := fun h => (Finset.disjoint_left.mp hSC) (hA h) hz₀
  have hrootnot : z₀ ∉ A ∪ Q e := by simp [hrootA,hrootnotQ]
  have hqC : q ∈ C := (Finset.mem_inter.mp hqE).2
  have hqA : q ∉ A := fun h => (Finset.disjoint_left.mp hSC) (hA h) hqC
  have hqQ : q ∉ Q e := fun h => (Finset.disjoint_left.mp hQeE) h hqE
  have hqroot : q ≠ z₀ := fun h => hrootnotB (h ▸ (Finset.mem_inter.mp hqE).1)
  have hqnot : q ∉ insert z₀ (A ∪ Q e) := by simp [hqroot,hqA,hqQ]
  have hsub : insert q (insert z₀ (A ∪ Q e)) ⊆ H.neighborFinset e := by
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_union] at ha
    rcases ha with rfl | rfl | ha | ha
    · simpa using heq
    · simpa using hrootedge
    · simpa using hBA e he a ha
    · simpa using hzQ e heC a ha
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hqnot,Finset.card_insert_of_notMem hrootnot,
    Finset.card_union_of_disjoint hAQ,hAcard,hQesize] at hc
  have hm := hmax e
  omega
