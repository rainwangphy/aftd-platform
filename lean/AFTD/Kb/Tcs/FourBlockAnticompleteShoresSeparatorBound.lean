import AFTD.Prelude

/-!
# four_block_anticomplete_shores_separator_bound

Topic: graphs   Node: 14af794840b0

Provenance: helper lemma. OP-1957: strengthened separator for arbitrary-sized four-block bridge shores.

In a finite four-block partition with A and B together of size L, C nonempty and anticomplete to D, suppose every separator has size at least L. For any disjoint anticomplete sets Q,W with D intersecting Q, the number of D vertices in Q or W plus the number of B vertices in W is at most the size of D.
-/

theorem four_block_anticomplete_shores_separator_bound
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B C D : Finset V)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hC : C.Nonempty) (L : ℕ) (hsizeAB : A.card+B.card=L)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hsep : ∀ X U V' : Finset V, U.Nonempty → V'.Nonempty →
      Disjoint X U → Disjoint X V' → Disjoint U V' → X ∪ U ∪ V' = Finset.univ →
      (∀ u ∈ U, ∀ v ∈ V', ¬ G.Adj u v) → L ≤ X.card)
    (Q W : Finset V) (hQW : Disjoint Q W)
    (hcross : ∀ q ∈ Q, ∀ w ∈ W, ¬ G.Adj q w)
    (hQD : (D ∩ Q).Nonempty) :
    (D ∩ Q).card + (B ∩ W).card + (D ∩ W).card ≤ D.card := by
  classical
  let X := A ∪ (B \ W) ∪ (D \ (Q ∪ W))
  let U := C ∪ (B ∩ W) ∪ (D ∩ W)
  let V := D ∩ Q
  have hUne : U.Nonempty := by
    obtain ⟨c,hc⟩ := hC
    exact ⟨c, by simp [U,hc]⟩
  have hVne : V.Nonempty := hQD
  have hXU : Disjoint X U := by
    apply Finset.disjoint_left.mpr
    intro v hv hu
    simp only [X, U, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter] at hv hu
    rcases hv with (hv | hv) | hv <;> rcases hu with (hu | hu) | hu
    · exact Finset.disjoint_left.mp hAC hv hu
    · exact Finset.disjoint_left.mp hAB hv hu.1
    · exact Finset.disjoint_left.mp hAD hv hu.1
    · exact Finset.disjoint_left.mp hBC hv.1 hu
    · exact hv.2 hu.2
    · exact Finset.disjoint_left.mp hBD hv.1 hu.1
    · exact Finset.disjoint_left.mp hCD hu hv.1
    · exact Finset.disjoint_left.mp hBD hu.1 hv.1
    · exact hv.2 (Or.inr hu.2)
  have hXV : Disjoint X V := by
    apply Finset.disjoint_left.mpr
    intro v hv hu
    simp only [X, V, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter] at hv hu
    rcases hv with (hv | hv) | hv
    · exact Finset.disjoint_left.mp hAD hv hu.1
    · exact Finset.disjoint_left.mp hBD hv.1 hu.1
    · exact hv.2 (Or.inl hu.2)
  have hUV : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro v hv hu
    simp only [U, V, Finset.mem_union, Finset.mem_inter] at hv hu
    rcases hv with (hv | hv) | hv
    · exact Finset.disjoint_left.mp hCD hv hu.1
    · exact Finset.disjoint_left.mp hBD hv.1 hu.1
    · exact Finset.disjoint_left.mp hQW hu.2 hv.2
  have hXUV : X ∪ U ∪ V = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro v
    have hall : v ∈ A ∨ v ∈ B ∨ v ∈ C ∨ v ∈ D := by
      have h : v ∈ A ∪ B ∪ C ∪ D := by rw [hcover]; exact Finset.mem_univ v
      simpa only [Finset.mem_union, or_assoc] using h
    rcases hall with ha | hb | hc | hd
    · simp [X,ha]
    · by_cases hw : v ∈ W <;> simp [X,U,hb,hw]
    · simp [U,hc]
    · by_cases hq : v ∈ Q
      · simp [V,hd,hq]
      · by_cases hw : v ∈ W <;> simp [X,U,hd,hq,hw]
  have hanti : ∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v := by
    intro u hu v hv huv
    simp only [U,V,Finset.mem_union,Finset.mem_inter] at hu hv
    rcases hu with (hu | hu) | hu
    · exact hnoCD u hu v hv.1 huv
    · exact hcross v hv.2 u hu.2 huv.symm
    · exact hcross v hv.2 u hu.2 huv.symm
  have hcut := hsep X U V hUne hVne hXU hXV hUV hXUV hanti
  have hXcard : X.card ≤ A.card + (B \ W).card + (D \ (Q ∪ W)).card :=
    (Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hBcard := Finset.card_sdiff_add_card_inter B W
  have hDcard := Finset.card_sdiff_add_card_inter D (Q ∪ W)
  have hDinter : D ∩ (Q ∪ W) = (D ∩ Q) ∪ (D ∩ W) := by
    exact Finset.inter_union_distrib_left D Q W
  have hDdis : Disjoint (D ∩ Q) (D ∩ W) := by
    exact Finset.disjoint_of_subset_left Finset.inter_subset_right
      (Finset.disjoint_of_subset_right Finset.inter_subset_right hQW)
  rw [hDinter, Finset.card_union_of_disjoint hDdis] at hDcard
  omega
