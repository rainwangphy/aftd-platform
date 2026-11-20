import AFTD.Prelude

/-!
# d11_eight_shore_cannot_target_nested_opposite

Topic: graphs   Node: 698fc358dce1

Provenance: helper lemma. OP-1957 factor-critical saturated-twin d=11 case; scratch Lean axiom audit completed.

The displayed d=11 nested-shore pattern contradicts the complement degree bound.
-/

theorem d11_eight_shore_cannot_target_nested_opposite
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y z₀ z q : V) (hxy : x ≠ y) (S C B : Finset V) (Q W : V → Finset V)
    (hSC : Disjoint S C) (hxC : x ∉ C) (hyC : y ∉ C)
    (hB : B ⊆ S ∪ C) (hBS : (B ∩ S).card ≤ 2)
    (hz₀ : z₀ ∈ C) (hQ₀ : Q z₀ = B) (hz : z ∈ C) (hqE : q ∈ B ∩ C)
    (hqQz : q ∈ Q z) (hWz8 : (W z).card=8) (hQqB : Q q ⊆ B)
    (hmax : ∀ v, (H.neighborFinset v).card ≤ 11)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y)
    (hW : ∀ v ∈ C, W v ⊆ S) (hsize : ∀ v ∈ C, (Q v).card+(W v).card=12)
    (hQ4 : ∀ v ∈ C, 4 ≤ (Q v).card)
    (hzQ : ∀ v ∈ C, ∀ u ∈ Q v, H.Adj v u)
    (hcross : ∀ v ∈ C, ∀ u ∈ Q v, ∀ w ∈ W v, H.Adj u w) : False := by
  classical
  have hqC : q ∈ C := (Finset.mem_inter.mp hqE).2
  have hqB : q ∈ B := (Finset.mem_inter.mp hqE).1
  have hrootnotB : z₀ ∉ B := by
    intro h
    exact (hzQ z₀ hz₀ z₀ (hQ₀.symm ▸ h)).ne rfl
  have hqroot : q ≠ z₀ := fun h => hrootnotB (h ▸ hqB)
  have hrootQq : z₀ ∉ Q q := fun h => hrootnotB (hQqB h)
  have hWqC : Disjoint (W z) C := by
    apply Finset.disjoint_left.mpr
    intro w hw hc
    exact (Finset.disjoint_left.mp hSC) (hW z hz hw) hc
  have hrootW : z₀ ∉ W z := fun h => (Finset.disjoint_left.mp hWqC) h hz₀
  have hQqCbound : (Q q ∩ C).card ≤ 2 := by
    have hdis : Disjoint (W z) (Q q ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hWqC) ha (Finset.mem_inter.mp hb).2
    have hrnot : z₀ ∉ (W z ∪ (Q q ∩ C)) := by simp [hrootW,hrootQq]
    have hrootedge : H.Adj q z₀ := (hzQ z₀ hz₀ q (hQ₀.symm ▸ hqB)).symm
    have hsub : insert z₀ (W z ∪ (Q q ∩ C)) ⊆ H.neighborFinset q := by
      intro a ha
      simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_inter] at ha
      rcases ha with rfl | ha | ⟨ha,_⟩
      · simpa using hrootedge
      · simpa using hcross z hz q hqQz a ha
      · simpa using hzQ q hqC a ha
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hrnot,Finset.card_union_of_disjoint hdis,hWz8] at hc
    have hm := hmax q
    omega
  have hQqSbound : (Q q ∩ S).card ≤ 2 := by
    have hs : Q q ∩ S ⊆ B ∩ S := by
      intro a ha
      exact Finset.mem_inter.mpr ⟨hQqB (Finset.mem_inter.mp ha).1,(Finset.mem_inter.mp ha).2⟩
    exact le_trans (Finset.card_le_card hs) hBS
  have hsplit : (Q q ∩ S).card + (Q q ∩ C).card = (Q q).card := by
    have hd : Disjoint (Q q ∩ S) (Q q ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hSC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
    have heq : (Q q ∩ S) ∪ (Q q ∩ C) = Q q := by
      ext a
      simp only [Finset.mem_union,Finset.mem_inter]
      constructor
      · rintro (⟨ha,_⟩ | ⟨ha,_⟩) <;> exact ha
      · intro ha
        rcases Finset.mem_union.mp (hB (hQqB ha)) with hs | hc
        · exact Or.inl ⟨ha,hs⟩
        · exact Or.inr ⟨ha,hc⟩
    have hc := congrArg Finset.card heq
    rw [Finset.card_union_of_disjoint hd] at hc
    exact hc
  have hQqsize : (Q q).card=4 := by have hq4 := hQ4 q hqC; omega
  have hWq8 : (W q).card=8 := by have hs := hsize q hqC; omega
  have hpos : 0 < (Q q ∩ S).card := by omega
  obtain ⟨b,hb⟩ := Finset.card_pos.mp hpos
  have hbQ : b ∈ Q q := (Finset.mem_inter.mp hb).1
  have hbS : b ∈ S := (Finset.mem_inter.mp hb).2
  have hbB : b ∈ B := hQqB hbQ
  have hxS : x ∉ S := by intro h; exact (hSxy x h).1.ne rfl
  have hyS : y ∉ S := by intro h; exact (hSxy y h).2.ne rfl
  have hxW : x ∉ W q := fun h => hxS (hW q hqC h)
  have hyW : y ∉ W q := fun h => hyS (hW q hqC h)
  have hrW : z₀ ∉ W q := fun h => (Finset.disjoint_left.mp hSC) (hW q hqC h) hz₀
  have hqW : q ∉ W q := fun h => (Finset.disjoint_left.mp hSC) (hW q hqC h) hqC
  have hxroot : x ≠ z₀ := fun h => hxC (h ▸ hz₀)
  have hyroot : y ≠ z₀ := fun h => hyC (h ▸ hz₀)
  have hxq : x ≠ q := fun h => hxC (h ▸ hqC)
  have hyq : y ≠ q := fun h => hyC (h ▸ hqC)
  have hrootq : z₀ ≠ q := hqroot.symm
  have hxnot : x ∉ insert y (insert z₀ (insert q (W q))) := by simp [hxy,hxroot,hxq,hxW]
  have hynot : y ∉ insert z₀ (insert q (W q)) := by simp [hyroot,hyq,hyW]
  have hrnot : z₀ ∉ insert q (W q) := by simp [hrootq,hrW]
  have hbx : H.Adj b x := (hSxy b hbS).1
  have hby : H.Adj b y := (hSxy b hbS).2
  have hbr : H.Adj b z₀ := (hzQ z₀ hz₀ b (hQ₀.symm ▸ hbB)).symm
  have hbq : H.Adj b q := (hzQ q hqC b hbQ).symm
  have hsub : insert x (insert y (insert z₀ (insert q (W q)))) ⊆ H.neighborFinset b := by
    intro a ha
    simp only [Finset.mem_insert] at ha
    rcases ha with rfl | rfl | rfl | rfl | ha
    · simpa using hbx
    · simpa using hby
    · simpa using hbr
    · simpa using hbq
    · simpa using hcross q hqC b hbQ a ha
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxnot,Finset.card_insert_of_notMem hynot,
    Finset.card_insert_of_notMem hrnot,Finset.card_insert_of_notMem hqW,hWq8] at hc
  have hm := hmax b
  omega
