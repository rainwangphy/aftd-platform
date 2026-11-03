import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteFamilyPackingIsDisjoint
import AFTD.Kb.Tcs.FiniteFamilyPointCover

/-!
# finite_family_disjoint_factor_two_gluing

Topic: graphs   Node: 8e8e5d0daebd

Provenance: helper lemma. Disjoint-side case of the published separator reduction, https://www.cs.tau.ac.il/~krivelev/2.pdf, Lemma 5.

Factor-two packing-cover certificates combine for disjoint finite families when every member from one family is disjoint from every member of the other.
-/

theorem finite_family_disjoint_factor_two_gluing {α : Type*} [DecidableEq α]
    (F₁ F₂ : Finset (Finset α))
    (hF : Disjoint F₁ F₂)
    (hcross : ∀ A ∈ F₁, ∀ B ∈ F₂, Disjoint A B)
    (h₁ : ∃ P C, finite_family_packing_is_disjoint F₁ P ∧ finite_family_point_cover F₁ C ∧ C.card ≤ 2 * P.card)
    (h₂ : ∃ P C, finite_family_packing_is_disjoint F₂ P ∧ finite_family_point_cover F₂ C ∧ C.card ≤ 2 * P.card) :
    ∃ P C, finite_family_packing_is_disjoint (F₁ ∪ F₂) P ∧
      finite_family_point_cover (F₁ ∪ F₂) C ∧ C.card ≤ 2 * P.card := by
  classical
  obtain ⟨P₁,C₁,⟨hP₁,hpack₁⟩,hc₁,hbound₁⟩ := h₁
  obtain ⟨P₂,C₂,⟨hP₂,hpack₂⟩,hc₂,hbound₂⟩ := h₂
  have hpdisj : Disjoint P₁ P₂ := Disjoint.mono hP₁ hP₂ hF
  have hpack : ((P₁ ∪ P₂ : Finset (Finset α)) : Set (Finset α)).Pairwise Disjoint := by
    rw [Finset.coe_union, Set.pairwise_union_of_symm]
    refine ⟨hpack₁,hpack₂,?_⟩
    intro A hA B hB _
    exact hcross A (hP₁ hA) B (hP₂ hB)
  have hc : finite_family_point_cover (F₁ ∪ F₂) (C₁ ∪ C₂) := by
    intro A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · obtain ⟨x,hxA,hxC⟩ := Finset.not_disjoint_iff.mp (hc₁ A hA)
      exact Finset.not_disjoint_iff.mpr ⟨x,hxA,Finset.mem_union_left _ hxC⟩
    · obtain ⟨x,hxA,hxC⟩ := Finset.not_disjoint_iff.mp (hc₂ A hA)
      exact Finset.not_disjoint_iff.mpr ⟨x,hxA,Finset.mem_union_right _ hxC⟩
  refine ⟨P₁ ∪ P₂,C₁ ∪ C₂,⟨Finset.union_subset_union hP₁ hP₂,hpack⟩,hc,?_⟩
  have hcard := Finset.card_union_le C₁ C₂
  rw [Finset.card_union_of_disjoint hpdisj]
  omega
