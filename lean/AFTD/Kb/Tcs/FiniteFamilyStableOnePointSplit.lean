import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteFamilyPackingIsDisjoint

/-!
# finite_family_stable_one_point_split

Topic: graphs   Node: dd731a6736df

Provenance: helper lemma. One-point family decomposition for the triangle-packing campaign, session IN-580.

If two finite set families meet only at one point, a maximum packing of their union avoiding that point restricts to a maximum packing of each side. If the union has a maximum packing avoiding each point, so does each side.
-/

lemma finite_family_stable_one_point_split_gluing_right {α : Type*} [DecidableEq α]
    (F₁ F₂ Q₁ P₂ : Finset (Finset α)) (p : α)
    (hcross : ∀ A ∈ F₁, ∀ B ∈ F₂, A ∩ B ⊆ {p})
    (hQ₁ : finite_family_packing_is_disjoint F₁ Q₁)
    (hP₂ : finite_family_packing_is_disjoint F₂ P₂)
    (havoid : ∀ B ∈ P₂, p ∉ B) :
    finite_family_packing_is_disjoint (F₁ ∪ F₂) (Q₁ ∪ P₂) := by
  rcases hQ₁ with ⟨hQ₁sub, hQ₁pack⟩
  rcases hP₂ with ⟨hP₂sub, hP₂pack⟩
  refine ⟨Finset.union_subset_union hQ₁sub hP₂sub, ?_⟩
  rw [Finset.coe_union, Set.pairwise_union_of_symm]
  refine ⟨hQ₁pack, hP₂pack, ?_⟩
  intro A hA B hB _
  rw [Finset.disjoint_iff_inter_eq_empty]
  apply Finset.subset_empty.mp
  intro x hx
  have hsub : A ∩ B ⊆ {p} := hcross A (hQ₁sub hA) B (hP₂sub hB)
  have hxp : x ∈ {p} := hsub hx
  simp only [Finset.mem_singleton] at hxp
  subst hxp
  exact (havoid B hB (Finset.mem_of_mem_inter_right hx)).elim

lemma finite_family_stable_one_point_split_gluing_left {α : Type*} [DecidableEq α]
    (F₁ F₂ P₁ Q₂ : Finset (Finset α)) (p : α)
    (hcross : ∀ A ∈ F₁, ∀ B ∈ F₂, A ∩ B ⊆ {p})
    (hP₁ : finite_family_packing_is_disjoint F₁ P₁)
    (hQ₂ : finite_family_packing_is_disjoint F₂ Q₂)
    (havoid : ∀ A ∈ P₁, p ∉ A) :
    finite_family_packing_is_disjoint (F₁ ∪ F₂) (P₁ ∪ Q₂) := by
  rcases hP₁ with ⟨hP₁sub, hP₁pack⟩
  rcases hQ₂ with ⟨hQ₂sub, hQ₂pack⟩
  refine ⟨Finset.union_subset_union hP₁sub hQ₂sub, ?_⟩
  rw [Finset.coe_union, Set.pairwise_union_of_symm]
  refine ⟨hP₁pack, hQ₂pack, ?_⟩
  intro A hA B hB _
  rw [Finset.disjoint_iff_inter_eq_empty]
  apply Finset.subset_empty.mp
  intro x hx
  have hsub : A ∩ B ⊆ {p} := hcross A (hP₁sub hA) B (hQ₂sub hB)
  have hxp : x ∈ {p} := hsub hx
  simp only [Finset.mem_singleton] at hxp
  subst hxp
  exact (havoid A hA (Finset.mem_of_mem_inter_left hx)).elim

lemma finite_family_stable_one_point_split_inter_left {α : Type*} [DecidableEq α]
    (F₁ F₂ P : Finset (Finset α))
    (hP : finite_family_packing_is_disjoint (F₁ ∪ F₂) P) :
    finite_family_packing_is_disjoint F₁ (P ∩ F₁) := by
  refine ⟨Finset.inter_subset_right, ?_⟩
  apply hP.2.mono
  intro A hA
  exact (Finset.mem_inter.mp hA).1

lemma finite_family_stable_one_point_split_inter_right {α : Type*} [DecidableEq α]
    (F₁ F₂ P : Finset (Finset α))
    (hP : finite_family_packing_is_disjoint (F₁ ∪ F₂) P) :
    finite_family_packing_is_disjoint F₂ (P ∩ F₂) := by
  refine ⟨Finset.inter_subset_right, ?_⟩
  apply hP.2.mono
  intro A hA
  exact (Finset.mem_inter.mp hA).1

lemma finite_family_stable_one_point_split_card_split {α : Type*} [DecidableEq α]
    (F₁ F₂ P : Finset (Finset α))
    (hP : P ⊆ F₁ ∪ F₂) (hF : Disjoint F₁ F₂) :
    (P ∩ F₁).card + (P ∩ F₂).card = P.card := by
  have h_dec : P = (P ∩ F₁) ∪ (P ∩ F₂) := by
    ext A
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hA
      have := hP hA
      simp only [Finset.mem_union] at this
      rcases this with h1 | h2
      · left; exact ⟨hA, h1⟩
      · right; exact ⟨hA, h2⟩
    · rintro (⟨hA, -⟩ | ⟨hA, -⟩) <;> exact hA
  have h_disj : Disjoint (P ∩ F₁) (P ∩ F₂) :=
    Disjoint.mono Finset.inter_subset_right Finset.inter_subset_right hF
  conv_rhs => rw [h_dec]
  rw [Finset.card_union_of_disjoint h_disj]

theorem finite_family_stable_one_point_split {α : Type*} [DecidableEq α]
    (F₁ F₂ : Finset (Finset α)) (p : α) (q : ℕ)
    (hF : Disjoint F₁ F₂)
    (hcross : ∀ A ∈ F₁, ∀ B ∈ F₂, A ∩ B ⊆ {p})
    (hbound : ∀ P, finite_family_packing_is_disjoint (F₁ ∪ F₂) P → P.card ≤ q)
    (hpoint : ∃ P, finite_family_packing_is_disjoint (F₁ ∪ F₂) P ∧
      P.card = q ∧ p ∉ P.biUnion id)
    (hstable : ∀ x ∈ (F₁ ∪ F₂).biUnion id, ∃ P,
      finite_family_packing_is_disjoint (F₁ ∪ F₂) P ∧ P.card = q ∧ x ∉ P.biUnion id) :
    ∃ k₁ k₂ : ℕ, q = k₁ + k₂ ∧
      (∀ P, finite_family_packing_is_disjoint F₁ P → P.card ≤ k₁) ∧
      (∀ P, finite_family_packing_is_disjoint F₂ P → P.card ≤ k₂) ∧
      (∀ x ∈ F₁.biUnion id, ∃ P, finite_family_packing_is_disjoint F₁ P ∧
        P.card = k₁ ∧ x ∉ P.biUnion id) ∧
      (∀ x ∈ F₂.biUnion id, ∃ P, finite_family_packing_is_disjoint F₂ P ∧
        P.card = k₂ ∧ x ∉ P.biUnion id) := by
  obtain ⟨P, hPpack, hPcard, hPavoid⟩ := hpoint
  have hPavoid' : ∀ A ∈ P, p ∉ A := by
    intro A hA hpA
    apply hPavoid
    exact Finset.mem_biUnion.mpr ⟨A, hA, hpA⟩
  have hP₁pack : finite_family_packing_is_disjoint F₁ (P ∩ F₁) :=
    finite_family_stable_one_point_split_inter_left F₁ F₂ P hPpack
  have hP₂pack : finite_family_packing_is_disjoint F₂ (P ∩ F₂) :=
    finite_family_stable_one_point_split_inter_right F₁ F₂ P hPpack
  have hP₁avoid : ∀ A ∈ P ∩ F₁, p ∉ A := fun A hA => hPavoid' A (Finset.mem_inter.mp hA).1
  have hP₂avoid : ∀ B ∈ P ∩ F₂, p ∉ B := fun B hB => hPavoid' B (Finset.mem_inter.mp hB).1
  have hq_sum : q = (P ∩ F₁).card + (P ∩ F₂).card := by
    have hsum := finite_family_stable_one_point_split_card_split F₁ F₂ P hPpack.1 hF
    omega
  have hbound₁ : ∀ Q, finite_family_packing_is_disjoint F₁ Q → Q.card ≤ (P ∩ F₁).card := by
    intro Q hQ
    have hQP₂ : finite_family_packing_is_disjoint (F₁ ∪ F₂) (Q ∪ (P ∩ F₂)) :=
      finite_family_stable_one_point_split_gluing_right F₁ F₂ Q (P ∩ F₂) p hcross hQ hP₂pack hP₂avoid
    have hcard_le := hbound (Q ∪ (P ∩ F₂)) hQP₂
    have hdisj : Disjoint Q (P ∩ F₂) :=
      Disjoint.mono hQ.1 Finset.inter_subset_right hF
    rw [Finset.card_union_of_disjoint hdisj] at hcard_le
    omega
  have hbound₂ : ∀ Q, finite_family_packing_is_disjoint F₂ Q → Q.card ≤ (P ∩ F₂).card := by
    intro Q hQ
    have hP₁Q : finite_family_packing_is_disjoint (F₁ ∪ F₂) ((P ∩ F₁) ∪ Q) :=
      finite_family_stable_one_point_split_gluing_left F₁ F₂ (P ∩ F₁) Q p hcross hP₁pack hQ hP₁avoid
    have hcard_le := hbound ((P ∩ F₁) ∪ Q) hP₁Q
    have hdisj : Disjoint (P ∩ F₁) Q :=
      Disjoint.mono Finset.inter_subset_right hQ.1 hF
    rw [Finset.card_union_of_disjoint hdisj] at hcard_le
    omega
  refine ⟨(P ∩ F₁).card, (P ∩ F₂).card, hq_sum, hbound₁, hbound₂, ?_, ?_⟩
  · intro x hx
    have hx_union : x ∈ (F₁ ∪ F₂).biUnion id := by
      obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_biUnion.mpr ⟨A, Finset.mem_union_left _ hA, hxA⟩
    obtain ⟨P', hP'pack, hP'card, hP'avoid⟩ := hstable x hx_union
    have hP'₁pack : finite_family_packing_is_disjoint F₁ (P' ∩ F₁) :=
      finite_family_stable_one_point_split_inter_left F₁ F₂ P' hP'pack
    have hP'₂pack : finite_family_packing_is_disjoint F₂ (P' ∩ F₂) :=
      finite_family_stable_one_point_split_inter_right F₁ F₂ P' hP'pack
    have hsplit := finite_family_stable_one_point_split_card_split F₁ F₂ P' hP'pack.1 hF
    have hle₁ := hbound₁ (P' ∩ F₁) hP'₁pack
    have hle₂ := hbound₂ (P' ∩ F₂) hP'₂pack
    have hcard₁ : (P' ∩ F₁).card = (P ∩ F₁).card := by omega
    refine ⟨P' ∩ F₁, hP'₁pack, hcard₁, ?_⟩
    intro hxP'₁
    apply hP'avoid
    obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.mp hxP'₁
    exact Finset.mem_biUnion.mpr ⟨A, (Finset.mem_inter.mp hA).1, hxA⟩
  · intro x hx
    have hx_union : x ∈ (F₁ ∪ F₂).biUnion id := by
      obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_biUnion.mpr ⟨A, Finset.mem_union_right _ hA, hxA⟩
    obtain ⟨P', hP'pack, hP'card, hP'avoid⟩ := hstable x hx_union
    have hP'₁pack : finite_family_packing_is_disjoint F₁ (P' ∩ F₁) :=
      finite_family_stable_one_point_split_inter_left F₁ F₂ P' hP'pack
    have hP'₂pack : finite_family_packing_is_disjoint F₂ (P' ∩ F₂) :=
      finite_family_stable_one_point_split_inter_right F₁ F₂ P' hP'pack
    have hsplit := finite_family_stable_one_point_split_card_split F₁ F₂ P' hP'pack.1 hF
    have hle₁ := hbound₁ (P' ∩ F₁) hP'₁pack
    have hle₂ := hbound₂ (P' ∩ F₂) hP'₂pack
    have hcard₂ : (P' ∩ F₂).card = (P ∩ F₂).card := by omega
    refine ⟨P' ∩ F₂, hP'₂pack, hcard₂, ?_⟩
    intro hxP'₂
    apply hP'avoid
    obtain ⟨A, hA, hxA⟩ := Finset.mem_biUnion.mp hxP'₂
    exact Finset.mem_biUnion.mpr ⟨A, (Finset.mem_inter.mp hA).1, hxA⟩
