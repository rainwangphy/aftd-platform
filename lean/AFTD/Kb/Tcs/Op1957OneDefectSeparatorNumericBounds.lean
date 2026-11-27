import AFTD.Prelude
import AFTD.Kb.Tcs.FourBlockAnticompleteShoresSeparatorBound

/-!
# op1957_one_defect_separator_numeric_bounds

Topic: graphs   Node: 44ea37fc9b66

Provenance: helper lemma. OP-1957: five-by-odd boundary reduction, arXiv:2611.22690

Under the displayed four-block partition and separator hypotheses, the two displayed D-shore count inequalities follow when the corresponding endpoint shore meets D.
-/

theorem op1957_one_defect_separator_numeric_bounds
    (k c : ℕ) (G : SimpleGraph (Fin (4*k)))
    (A B C D X Y U : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hsizeAB : A.card+B.card=2*k) (hD : D.card+c=2*k)
    (hnoCD : ∀ a ∈ C, ∀ b ∈ D, ¬ G.Adj a b)
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (x y : Fin (4*k)) (hxA : x ∈ A) (hyC : y ∈ C) (hxX : x ∈ X) (hyY : y ∈ Y)
    (hXY : Disjoint X Y) (hXU : Disjoint X U) (hYU : Disjoint Y U)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hantiX : ∀ a ∈ X, ∀ u ∈ U, ¬ G.Adj a u)
    (hantiY : ∀ a ∈ Y, ∀ u ∈ U, ¬ G.Adj a u) :
    (1 ≤ (X ∩ D).card → (X ∩ D).card+(Y ∩ B).card+(Y ∩ D).card+(U ∩ B).card+(U ∩ D).card+c ≤ 2*k) ∧
    (1 ≤ (Y ∩ D).card → (Y ∩ D).card+(X ∩ B).card+(X ∩ D).card+(U ∩ B).card+(U ∩ D).card+c ≤ 2*k) := by
  classical
  have hxB : x ∉ B := fun h => Finset.disjoint_left.mp hAB hxA h
  have hyB : y ∉ B := fun h => Finset.disjoint_left.mp hBC h hyC
  have hxD : x ∉ D := fun h => Finset.disjoint_left.mp hAD hxA h
  have hyD : y ∉ D := fun h => Finset.disjoint_left.mp hCD hyC h
  constructor
  · intro hh
    let W := Y.erase y ∪ U
    have hd : (D ∩ X).Nonempty := by
      apply Finset.card_pos.mp
      simpa [Finset.inter_comm] using hh
    have hdis : Disjoint X W := by
      dsimp [W]
      exact Finset.disjoint_union_right.mpr ⟨Finset.disjoint_of_subset_right (Finset.erase_subset y Y) hXY,hXU⟩
    have hanti : ∀ u ∈ X, ∀ v ∈ W, ¬ G.Adj u v := by
      intro u hu v hv h
      rcases Finset.mem_union.mp hv with hv | hv
      · have hv' := Finset.mem_erase.mp hv
        exact hv'.1 (hcross u hu v hv'.2 h).2
      · exact hantiX u hu v hv h
    have hB_Y : B ∩ Y.erase y = B ∩ Y := by
      ext v; simp only [Finset.mem_inter,Finset.mem_erase]
      constructor
      · rintro ⟨hb,_,hy⟩; exact ⟨hb,hy⟩
      · rintro ⟨hb,hy⟩; exact ⟨hb,fun h => hyB (h ▸ hb),hy⟩
    have hD_Y : D ∩ Y.erase y = D ∩ Y := by
      ext v; simp only [Finset.mem_inter,Finset.mem_erase]
      constructor
      · rintro ⟨hd,_,hy⟩; exact ⟨hd,hy⟩
      · rintro ⟨hd,hy⟩; exact ⟨hd,fun h => hyD (h ▸ hd),hy⟩
    have hBW : (B ∩ W).card = (Y ∩ B).card+(U ∩ B).card := by
      dsimp [W]
      rw [Finset.inter_union_distrib_left,hB_Y,Finset.card_union_of_disjoint]
      · rw [Finset.inter_comm B Y,Finset.inter_comm B U]
      · exact Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right hYU)
    have hDW : (D ∩ W).card = (Y ∩ D).card+(U ∩ D).card := by
      dsimp [W]
      rw [Finset.inter_union_distrib_left,hD_Y,Finset.card_union_of_disjoint]
      · rw [Finset.inter_comm D Y,Finset.inter_comm D U]
      · exact Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right hYU)
    have hb := four_block_anticomplete_shores_separator_bound G A B C D
      hAB hAC hAD hBC hBD hCD hcover ⟨y,hyC⟩ (2*k) hsizeAB hnoCD hsep X W hdis hanti hd
    rw [hBW,hDW,Finset.inter_comm D X] at hb
    omega
  · intro hh
    let W := X.erase x ∪ U
    have hd : (D ∩ Y).Nonempty := by
      apply Finset.card_pos.mp
      simpa [Finset.inter_comm] using hh
    have hdis : Disjoint Y W := by
      dsimp [W]
      exact Finset.disjoint_union_right.mpr ⟨Finset.disjoint_of_subset_right (Finset.erase_subset x X) hXY.symm,hYU⟩
    have hanti : ∀ u ∈ Y, ∀ v ∈ W, ¬ G.Adj u v := by
      intro u hu v hv h
      rcases Finset.mem_union.mp hv with hv | hv
      · have hv' := Finset.mem_erase.mp hv
        exact hv'.1 (hcross v hv'.2 u hu h.symm).1
      · exact hantiY u hu v hv h
    have hB_X : B ∩ X.erase x = B ∩ X := by
      ext v; simp only [Finset.mem_inter,Finset.mem_erase]
      constructor
      · rintro ⟨hb,_,hx⟩; exact ⟨hb,hx⟩
      · rintro ⟨hb,hx⟩; exact ⟨hb,fun h => hxB (h ▸ hb),hx⟩
    have hD_X : D ∩ X.erase x = D ∩ X := by
      ext v; simp only [Finset.mem_inter,Finset.mem_erase]
      constructor
      · rintro ⟨hd,_,hx⟩; exact ⟨hd,hx⟩
      · rintro ⟨hd,hx⟩; exact ⟨hd,fun h => hxD (h ▸ hd),hx⟩
    have hBW : (B ∩ W).card = (X ∩ B).card+(U ∩ B).card := by
      dsimp [W]
      rw [Finset.inter_union_distrib_left,hB_X,Finset.card_union_of_disjoint]
      · rw [Finset.inter_comm B X,Finset.inter_comm B U]
      · exact Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right hXU)
    have hDW : (D ∩ W).card = (X ∩ D).card+(U ∩ D).card := by
      dsimp [W]
      rw [Finset.inter_union_distrib_left,hD_X,Finset.card_union_of_disjoint]
      · rw [Finset.inter_comm D X,Finset.inter_comm D U]
      · exact Finset.disjoint_of_subset_left Finset.inter_subset_right
          (Finset.disjoint_of_subset_right Finset.inter_subset_right hXU)
    have hb := four_block_anticomplete_shores_separator_bound G A B C D
      hAB hAC hAD hBC hBD hCD hcover ⟨y,hyC⟩ (2*k) hsizeAB hnoCD hsep Y W hdis hanti hd
    rw [hBW,hDW,Finset.inter_comm D Y] at hb
    omega
