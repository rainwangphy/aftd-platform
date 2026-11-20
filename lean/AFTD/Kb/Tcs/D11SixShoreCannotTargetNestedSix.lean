import AFTD.Prelude

/-!
# d11_six_shore_cannot_target_nested_six

Topic: graphs   Node: 7f8455e8ea35

Provenance: helper lemma. OP-1957 factor-critical saturated-twin d=11 case; scratch Lean axiom audit completed.

The displayed d=11 nested-shore pattern contradicts the complement degree bound.
-/

theorem d11_six_shore_cannot_target_nested_six
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (z₀ z q : V) (S C B : Finset V) (Q W : V → Finset V)
    (hSC : Disjoint S C) (hB : B ⊆ S ∪ C) (hBcard : B.card=8)
    (hBS : (B ∩ S).card ≤ 2)
    (hz₀ : z₀ ∈ C) (hQ₀ : Q z₀ = B) (hzE : z ∈ B ∩ C) (hqE : q ∈ B ∩ C)
    (hqQz : q ∈ Q z) (hWz6 : (W z).card=6) (hWq6 : (W q).card=6)
    (hQzB : Q z ⊆ B) (hQqB : Q q ⊆ B)
    (hmax : ∀ v, (H.neighborFinset v).card ≤ 11)
    (hW : ∀ v ∈ C, W v ⊆ S) (hdis : ∀ v ∈ C, Disjoint (Q v) (W v))
    (hsize : ∀ v ∈ C, (Q v).card+(W v).card=12)
    (hzQ : ∀ v ∈ C, ∀ u ∈ Q v, H.Adj v u)
    (hcross : ∀ v ∈ C, ∀ u ∈ Q v, ∀ w ∈ W v, H.Adj u w) : False := by
  classical
  have hzC : z ∈ C := (Finset.mem_inter.mp hzE).2
  have hzB : z ∈ B := (Finset.mem_inter.mp hzE).1
  have hqC : q ∈ C := (Finset.mem_inter.mp hqE).2
  have hqB : q ∈ B := (Finset.mem_inter.mp hqE).1
  have hrootnotB : z₀ ∉ B := by
    intro h
    exact (hzQ z₀ hz₀ z₀ (hQ₀.symm ▸ h)).ne rfl
  have hrootQq : z₀ ∉ Q q := fun h => hrootnotB (hQqB h)
  have hWzC : Disjoint (W z) C := by
    apply Finset.disjoint_left.mpr
    intro w hw hc
    exact (Finset.disjoint_left.mp hSC) (hW z hzC hw) hc
  have hrootW : z₀ ∉ W z := fun h => (Finset.disjoint_left.mp hWzC) h hz₀
  have hQqsize : (Q q).card=6 := by have hs := hsize q hqC; omega
  have hQzsize : (Q z).card=6 := by have hs := hsize z hzC; omega
  have hQqCbound : (Q q ∩ C).card ≤ 4 := by
    have hd : Disjoint (W z) (Q q ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hWzC) ha (Finset.mem_inter.mp hb).2
    have hrnot : z₀ ∉ W z ∪ (Q q ∩ C) := by simp [hrootW,hrootQq]
    have hrootedge : H.Adj q z₀ := (hzQ z₀ hz₀ q (hQ₀.symm ▸ hqB)).symm
    have hsub : insert z₀ (W z ∪ (Q q ∩ C)) ⊆ H.neighborFinset q := by
      intro a ha
      simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_inter] at ha
      rcases ha with rfl | ha | ⟨ha,_⟩
      · simpa using hrootedge
      · simpa using hcross z hzC q hqQz a ha
      · simpa using hzQ q hqC a ha
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hrnot,Finset.card_union_of_disjoint hd,hWz6] at hc
    have hm := hmax q
    omega
  have hQqSsub : Q q ∩ S ⊆ B ∩ S := by
    intro a ha
    exact Finset.mem_inter.mpr ⟨hQqB (Finset.mem_inter.mp ha).1,(Finset.mem_inter.mp ha).2⟩
  have hQqSbound : (Q q ∩ S).card ≤ 2 := le_trans (Finset.card_le_card hQqSsub) hBS
  have hsplit (T : Finset V) (hTB : T ⊆ B) : (T ∩ S).card+(T ∩ C).card=T.card := by
    have hd : Disjoint (T ∩ S) (T ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hSC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
    have heq : (T ∩ S) ∪ (T ∩ C) = T := by
      ext a
      simp only [Finset.mem_union,Finset.mem_inter]
      constructor
      · rintro (⟨ha,_⟩ | ⟨ha,_⟩) <;> exact ha
      · intro ha
        rcases Finset.mem_union.mp (hB (hTB ha)) with hs | hc
        · exact Or.inl ⟨ha,hs⟩
        · exact Or.inr ⟨ha,hc⟩
    have hc := congrArg Finset.card heq
    rw [Finset.card_union_of_disjoint hd] at hc
    exact hc
  have hQsplit := hsplit (Q q) hQqB
  have hBsplit := hsplit B (Finset.Subset.rfl)
  have hQqCsize : (Q q ∩ C).card=4 := by omega
  have hQqSP := Finset.card_le_card hQqSsub
  have hPsize : (B ∩ S).card=2 := by omega
  have hEsize : (B ∩ C).card=6 := by omega
  have hPsub : B ∩ S ⊆ Q q := by
    have heq : Q q ∩ S = B ∩ S := Finset.eq_of_subset_of_card_le hQqSsub (by omega)
    intro a ha
    exact (Finset.mem_inter.mp (heq.symm ▸ ha)).1
  let N := insert z₀ (W z ∪ (Q q ∩ C))
  have hrootedge : H.Adj q z₀ := (hzQ z₀ hz₀ q (hQ₀.symm ▸ hqB)).symm
  have hNsub : N ⊆ H.neighborFinset q := by
    intro a ha
    dsimp [N] at ha
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_inter] at ha
    rcases ha with rfl | ha | ⟨ha,_⟩
    · simpa using hrootedge
    · simpa using hcross z hzC q hqQz a ha
    · simpa using hzQ q hqC a ha
  have hNsize : N.card=11 := by
    have hd : Disjoint (W z) (Q q ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hWzC) ha (Finset.mem_inter.mp hb).2
    have hrnot : z₀ ∉ W z ∪ (Q q ∩ C) := by simp [hrootW,hrootQq]
    dsimp [N]
    rw [Finset.card_insert_of_notMem hrnot,Finset.card_union_of_disjoint hd,hWz6,hQqCsize]
  have hNeq : N = H.neighborFinset q := Finset.eq_of_subset_of_card_le hNsub (by rw [hNsize]; exact hmax q)
  have hP_W : B ∩ S ⊆ W z := by
    intro a ha
    have haQ : a ∈ Q q := hPsub ha
    have haN : a ∈ N := hNeq.symm ▸ ((H.mem_neighborFinset q a).mpr (hzQ q hqC a haQ))
    have haS : a ∈ S := (Finset.mem_inter.mp ha).2
    have haC : a ∉ C := fun h => (Finset.disjoint_left.mp hSC) haS h
    dsimp [N] at haN
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_inter] at haN
    rcases haN with heq | hw | ⟨_,hc⟩
    · exact (haC (heq ▸ hz₀)).elim
    · exact hw
    · exact (haC hc).elim
  have hQzE : Q z ⊆ B ∩ C := by
    intro a ha
    refine Finset.mem_inter.mpr ⟨hQzB ha,?_⟩
    rcases Finset.mem_union.mp (hB (hQzB ha)) with haS | haC
    · have haP : a ∈ B ∩ S := Finset.mem_inter.mpr ⟨hQzB ha,haS⟩
      exact ((Finset.disjoint_left.mp (hdis z hzC)) ha (hP_W haP)).elim
    · exact haC
  have hznotQ : z ∉ Q z := by
    intro h
    exact (hzQ z hzC z h).ne rfl
  have hsub : Q z ⊆ (B ∩ C).erase z := by
    intro a ha
    exact Finset.mem_erase.mpr ⟨fun h => hznotQ (h ▸ ha),hQzE ha⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hzE,hQzsize,hEsize] at hc
  omega
