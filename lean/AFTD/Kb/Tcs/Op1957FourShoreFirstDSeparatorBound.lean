import AFTD.Prelude
import AFTD.Kb.Tcs.FourBlockAnticompleteShoresSeparatorBound

/-!
# op1957_four_shore_first_D_separator_bound

Topic: graphs   Node: 6a910c855378

Provenance: helper lemma. OP-1957; positive-separator graph-to-count transfer.

Four shore first d separator bound.
-/

set_option maxHeartbeats 2000000

theorem op1957_four_shore_first_D_separator_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (F : Fin 4 → Finset V) (E A B C D : Finset V) (x y : V) (L : ℕ)
    (hFdis : ∀ i j : Fin 4, i ≠ j → Disjoint (F i) (F j))
    (hEdis : ∀ i : Fin 4, Disjoint (F i) E)
    (hcross : ∀ i j : Fin 4, i ≠ j → ∀ a ∈ F i, ∀ b ∈ F j, G.Adj a b →
      (i=0 ∧ j=1 ∧ a=x ∧ b=y) ∨ (i=1 ∧ j=0 ∧ a=y ∧ b=x))
    (hEanti : ∀ i : Fin 4, ∀ a ∈ F i, ∀ b ∈ E, ¬ G.Adj a b)
    (hEB : E ⊆ B) (hyC : y ∈ C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ) (hsize : A.card+B.card=L)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hsep : ∀ S P Q : Finset V, P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ a ∈ P, ∀ b ∈ Q, ¬ G.Adj a b) → L ≤ S.card)
    (hDpos : (D ∩ F 0).Nonempty) :
    (F 0 ∩ D).card + (F 1 ∩ B).card + (F 2 ∩ B).card +
      (F 3 ∩ B).card + E.card ≤ D.card := by
  classical
  let W := (F 1).erase y ∪ F 2 ∪ F 3 ∪ E
  have h0W : Disjoint (F 0) W := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    simp only [W,Finset.mem_union,Finset.mem_erase] at hw
    rcases hw with (((⟨_,hw⟩ | hw) | hw) | hw)
    · exact Finset.disjoint_left.mp (hFdis 0 1 (by decide)) hv hw
    · exact Finset.disjoint_left.mp (hFdis 0 2 (by decide)) hv hw
    · exact Finset.disjoint_left.mp (hFdis 0 3 (by decide)) hv hw
    · exact Finset.disjoint_left.mp (hEdis 0) hv hw
  have hanti : ∀ a ∈ F 0, ∀ b ∈ W, ¬ G.Adj a b := by
    intro a ha b hb hab
    simp only [W,Finset.mem_union,Finset.mem_erase] at hb
    rcases hb with (((⟨hby,hb⟩ | hb) | hb) | hb)
    · have hh := hcross 0 1 (by decide) a ha b hb hab
      have hh' : a=x ∧ b=y := by simpa using hh
      exact hby hh'.2
    · have hh := hcross 0 2 (by decide) a ha b hb hab
      simp at hh
    · have hh := hcross 0 3 (by decide) a ha b hb hab
      simp at hh
    · exact hEanti 0 a ha b hb hab
  have hcut := four_block_anticomplete_shores_separator_bound G A B C D
    hAB hAC hAD hBC hBD hCD hcover ⟨y,hyC⟩ L hsize hnoCD hsep (F 0) W h0W hanti hDpos
  let H1 := F 1 ∩ B
  let H2 := F 2 ∩ B
  let H3 := F 3 ∩ B
  have hyB : y ∉ B := fun h => Finset.disjoint_left.mp hBC h hyC
  have hWB : W ∩ B = H1 ∪ H2 ∪ H3 ∪ E := by
    ext v
    simp only [W,H1,H2,H3,Finset.mem_inter,Finset.mem_union,Finset.mem_erase]
    constructor
    · rintro ⟨(((⟨_,h1⟩ | h2) | h3) | he),hb⟩
      · exact Or.inl (Or.inl (Or.inl ⟨h1,hb⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨h2,hb⟩))
      · exact Or.inl (Or.inr ⟨h3,hb⟩)
      · exact Or.inr he
    · rintro (((⟨h1,hb⟩ | ⟨h2,hb⟩) | ⟨h3,hb⟩) | he)
      · exact ⟨Or.inl (Or.inl (Or.inl ⟨fun h => hyB (h ▸ hb),h1⟩)),hb⟩
      · exact ⟨Or.inl (Or.inl (Or.inr h2)),hb⟩
      · exact ⟨Or.inl (Or.inr h3),hb⟩
      · exact ⟨Or.inr he,hEB he⟩
  have h12 : Disjoint H1 H2 := Finset.disjoint_of_subset_left Finset.inter_subset_left
    (Finset.disjoint_of_subset_right Finset.inter_subset_left (hFdis 1 2 (by decide)))
  have h13 : Disjoint H1 H3 := Finset.disjoint_of_subset_left Finset.inter_subset_left
    (Finset.disjoint_of_subset_right Finset.inter_subset_left (hFdis 1 3 (by decide)))
  have h23 : Disjoint H2 H3 := Finset.disjoint_of_subset_left Finset.inter_subset_left
    (Finset.disjoint_of_subset_right Finset.inter_subset_left (hFdis 2 3 (by decide)))
  have h1E : Disjoint H1 E := Finset.disjoint_of_subset_left Finset.inter_subset_left (hEdis 1)
  have h2E : Disjoint H2 E := Finset.disjoint_of_subset_left Finset.inter_subset_left (hEdis 2)
  have h3E : Disjoint H3 E := Finset.disjoint_of_subset_left Finset.inter_subset_left (hEdis 3)
  have h123 : Disjoint (H1 ∪ H2) H3 := Finset.disjoint_union_left.mpr ⟨h13,h23⟩
  have h123E : Disjoint (H1 ∪ H2 ∪ H3) E :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨h1E,h2E⟩,h3E⟩
  rw [Finset.inter_comm B W,hWB,Finset.card_union_of_disjoint h123E,Finset.card_union_of_disjoint h123,
    Finset.card_union_of_disjoint h12,Finset.inter_comm D (F 0)] at hcut
  dsimp [H1,H2,H3] at hcut
  omega
