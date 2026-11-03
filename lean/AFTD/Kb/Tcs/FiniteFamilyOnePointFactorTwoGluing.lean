import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteFamilyPackingIsDisjoint
import AFTD.Kb.Tcs.FiniteFamilyPointCover

/-!
# finite_family_one_point_factor_two_gluing

Topic: graphs   Node: fba3ad93ebeb

Provenance: helper lemma. Published one-point separator reduction, https://www.cs.tau.ac.il/~krivelev/2.pdf, Lemma 5; finite-family formulation used in the triangle packing campaign.

For two disjoint finite set families whose cross intersections lie in one point, factor-two packing-cover certificates for both families and their point-deleted families give such a certificate for their union.
-/

private theorem in519_drop_point_packing {α : Type*} [DecidableEq α]
    (P : Finset (Finset α)) (p : α)
    (hP : (P : Set (Finset α)).Pairwise Disjoint) :
    P.card ≤ (P.filter (fun A => p ∉ A)).card + 1 := by
  classical
  have hsmall : (P.filter (fun A => p ∈ A)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro A hA B hB
    have hA' := Finset.mem_filter.mp hA
    have hB' := Finset.mem_filter.mp hB
    by_contra hne
    exact Finset.disjoint_left.mp (hP hA'.1 hB'.1 hne) hA'.2 hB'.2
  have hparts := Finset.card_filter_add_card_filter_not (s := P) (fun A => p ∈ A)
  omega

private theorem in519_cross_disjoint {α : Type*} [DecidableEq α]
    (F₁ F₂ : Finset (Finset α)) (p : α)
    (hcross : ∀ A ∈ F₁, ∀ B ∈ F₂, A ∩ B ⊆ {p})
    {A B : Finset α} (hA : A ∈ F₁) (hB : B ∈ F₂)
    (havoid : p ∉ A ∨ p ∉ B) : Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  have hx := hcross A hA B hB (Finset.mem_inter.mpr ⟨hxA,hxB⟩)
  have hxp : x = p := Finset.mem_singleton.mp hx
  subst x
  exact havoid.elim (fun h => h hxA) (fun h => h hxB)

private theorem in519_union_packing {α : Type*} [DecidableEq α]
    (F₁ F₂ P₁ P₂ : Finset (Finset α)) (p : α)
    (hF : Disjoint F₁ F₂)
    (hcross : ∀ A ∈ F₁, ∀ B ∈ F₂, A ∩ B ⊆ {p})
    (hsub₁ : P₁ ⊆ F₁) (hsub₂ : P₂ ⊆ F₂)
    (hpack₁ : (P₁ : Set (Finset α)).Pairwise Disjoint)
    (hpack₂ : (P₂ : Set (Finset α)).Pairwise Disjoint)
    (havoid : (∀ A ∈ P₁, p ∉ A) ∨ ∀ B ∈ P₂, p ∉ B) :
    (P₁ ∪ P₂ ⊆ F₁ ∪ F₂) ∧
      ((P₁ ∪ P₂ : Finset (Finset α)) : Set (Finset α)).Pairwise Disjoint ∧
      (P₁ ∪ P₂).card = P₁.card + P₂.card := by
  have hdisj : Disjoint P₁ P₂ := Disjoint.mono hsub₁ hsub₂ hF
  refine ⟨Finset.union_subset_union hsub₁ hsub₂, ?_, Finset.card_union_of_disjoint hdisj⟩
  rw [Finset.coe_union, Set.pairwise_union_of_symm]
  refine ⟨hpack₁, hpack₂, ?_⟩
  intro A hA B hB _
  apply in519_cross_disjoint F₁ F₂ p hcross (hsub₁ hA) (hsub₂ hB)
  exact havoid.elim (fun h => Or.inl (h A hA)) (fun h => Or.inr (h B hB))


private theorem in519_cover_union {α : Type*} [DecidableEq α]
    (F₁ F₂ : Finset (Finset α)) (C₁ C₂ : Finset α)
    (h₁ : finite_family_point_cover F₁ C₁) (h₂ : finite_family_point_cover F₂ C₂) :
    finite_family_point_cover (F₁ ∪ F₂) (C₁ ∪ C₂) := by
  intro A hA
  rcases Finset.mem_union.mp hA with hA | hA
  · obtain ⟨x, hxA, hxC⟩ := Finset.not_disjoint_iff.mp (h₁ A hA)
    exact Finset.not_disjoint_iff.mpr ⟨x, hxA, Finset.mem_union_left _ hxC⟩
  · obtain ⟨x, hxA, hxC⟩ := Finset.not_disjoint_iff.mp (h₂ A hA)
    exact Finset.not_disjoint_iff.mpr ⟨x, hxA, Finset.mem_union_right _ hxC⟩

private theorem in519_cover_insert_from_deleted {α : Type*} [DecidableEq α]
    (F₁ F₂ : Finset (Finset α)) (p : α) (D₁ D₂ : Finset α)
    (h₁ : finite_family_point_cover (F₁.filter (fun A => p ∉ A)) D₁)
    (h₂ : finite_family_point_cover (F₂.filter (fun A => p ∉ A)) D₂) :
    finite_family_point_cover (F₁ ∪ F₂) (insert p (D₁ ∪ D₂)) := by
  intro A hA
  by_cases hp : p ∈ A
  · exact Finset.not_disjoint_iff.mpr ⟨p, hp, Finset.mem_insert_self _ _⟩
  · have hd : ¬ Disjoint A (D₁ ∪ D₂) := by
      apply in519_cover_union _ _ _ _ h₁ h₂ A
      rcases Finset.mem_union.mp hA with hA | hA
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hA,hp⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hA,hp⟩)
    obtain ⟨x, hxA, hxD⟩ := Finset.not_disjoint_iff.mp hd
    exact Finset.not_disjoint_iff.mpr ⟨x,hxA,Finset.mem_insert_of_mem hxD⟩

theorem finite_family_one_point_factor_two_gluing {α : Type*} [DecidableEq α]
    (F₁ F₂ : Finset (Finset α)) (p : α)
    (hF : Disjoint F₁ F₂)
    (hcross : ∀ A ∈ F₁, ∀ B ∈ F₂, A ∩ B ⊆ {p})
    (h₁ : ∃ P C, finite_family_packing_is_disjoint F₁ P ∧ finite_family_point_cover F₁ C ∧ C.card ≤ 2 * P.card)
    (h₂ : ∃ P C, finite_family_packing_is_disjoint F₂ P ∧ finite_family_point_cover F₂ C ∧ C.card ≤ 2 * P.card)
    (h₁del : ∃ P C, finite_family_packing_is_disjoint (F₁.filter (fun A => p ∉ A)) P ∧
      finite_family_point_cover (F₁.filter (fun A => p ∉ A)) C ∧ C.card ≤ 2 * P.card)
    (h₂del : ∃ P C, finite_family_packing_is_disjoint (F₂.filter (fun A => p ∉ A)) P ∧
      finite_family_point_cover (F₂.filter (fun A => p ∉ A)) C ∧ C.card ≤ 2 * P.card) :
    ∃ P C, finite_family_packing_is_disjoint (F₁ ∪ F₂) P ∧ finite_family_point_cover (F₁ ∪ F₂) C ∧ C.card ≤ 2 * P.card := by
  classical
  obtain ⟨P₁,C₁,⟨hP₁,hpack₁⟩,hc₁,hbound₁⟩ := h₁
  obtain ⟨P₂,C₂,⟨hP₂,hpack₂⟩,hc₂,hbound₂⟩ := h₂
  obtain ⟨Q₁,D₁,⟨hQ₁,hqpack₁⟩,hd₁,hdbound₁⟩ := h₁del
  obtain ⟨Q₂,D₂,⟨hQ₂,hqpack₂⟩,hd₂,hdbound₂⟩ := h₂del
  have hQ₁sub : Q₁ ⊆ F₁ := (hQ₁.trans (Finset.filter_subset _ _))
  have hQ₂sub : Q₂ ⊆ F₂ := (hQ₂.trans (Finset.filter_subset _ _))
  have hQ₁avoid : ∀ A ∈ Q₁, p ∉ A := by
    intro A hA
    exact (Finset.mem_filter.mp (hQ₁ hA)).2
  have hQ₂avoid : ∀ A ∈ Q₂, p ∉ A := by
    intro A hA
    exact (Finset.mem_filter.mp (hQ₂ hA)).2
  by_cases hlarge₁ : P₁.card ≤ Q₁.card
  · have hp := in519_union_packing F₁ F₂ Q₁ P₂ p hF hcross hQ₁sub hP₂ hqpack₁ hpack₂ (Or.inl hQ₁avoid)
    refine ⟨Q₁ ∪ P₂, C₁ ∪ C₂, ⟨hp.1,hp.2.1⟩, in519_cover_union _ _ _ _ hc₁ hc₂, ?_⟩
    have hc := Finset.card_union_le C₁ C₂
    rw [hp.2.2]
    omega
  by_cases hlarge₂ : P₂.card ≤ Q₂.card
  · have hp := in519_union_packing F₁ F₂ P₁ Q₂ p hF hcross hP₁ hQ₂sub hpack₁ hqpack₂ (Or.inr hQ₂avoid)
    refine ⟨P₁ ∪ Q₂, C₁ ∪ C₂, ⟨hp.1,hp.2.1⟩, in519_cover_union _ _ _ _ hc₁ hc₂, ?_⟩
    have hc := Finset.card_union_le C₁ C₂
    rw [hp.2.2]
    omega
  let R := P₂.filter (fun A => p ∉ A)
  have hRsub : R ⊆ F₂ := (Finset.filter_subset _ _).trans hP₂
  have hRpack : (R : Set (Finset α)).Pairwise Disjoint := by
    apply hpack₂.mono
    intro A hA
    exact (Finset.mem_filter.mp hA).1
  have hRavoid : ∀ A ∈ R, p ∉ A := by
    intro A hA
    exact (Finset.mem_filter.mp hA).2
  have hRcard : P₂.card ≤ R.card + 1 := in519_drop_point_packing P₂ p hpack₂
  have hp := in519_union_packing F₁ F₂ P₁ R p hF hcross hP₁ hRsub hpack₁ hRpack (Or.inr hRavoid)
  refine ⟨P₁ ∪ R, insert p (D₁ ∪ D₂), ⟨hp.1,hp.2.1⟩,
    in519_cover_insert_from_deleted _ _ _ _ _ hd₁ hd₂, ?_⟩
  have hc := Finset.card_union_le D₁ D₂
  have hi := Finset.card_insert_le p (D₁ ∪ D₂)
  rw [hp.2.2]
  omega
