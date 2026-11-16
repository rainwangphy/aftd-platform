import AFTD.Prelude

/-!
# poset_down_set_preserving_bijective_eq

Topic: combinatorics   Node: eb5f9cb67abf

Provenance: helper lemma. arXiv:2611.15540, Lemma 3.1: Solutions of the set-theoretic quantum Yang-Baxter equation arising from posets

Let P and Q be finite posets, and let α, β : P → Q be bijective maps. If for all x in P, the image under α of the principal down-set Set.Iic x equals the principal down-set Set.Iic (β x), then α = β.
-/

/-- Two bijections between finite posets matching images of principal down-sets are equal. -/
theorem poset_down_set_preserving_bijective_eq
    {P Q : Type*} [Fintype P] [Fintype Q] [PartialOrder P] [PartialOrder Q]
    (α β : P → Q) (hα : Function.Bijective α) (hβ : Function.Bijective β)
    (h_down : ∀ x : P, α '' Set.Iic x = Set.Iic (β x)) :
    α = β := by
  classical
  have hcard_lt : ∀ x y : P, y < x → (Set.Iic y).ncard < (Set.Iic x).ncard := by
    intro x y hyx
    have hss : Set.Iic y ⊂ Set.Iic x := by
      rw [Set.ssubset_iff_subset_ne]
      constructor
      · intro z hz
        exact le_trans hz hyx.le
      · intro heq
        have hxmem : x ∈ Set.Iic x := le_rfl
        have : x ∈ Set.Iic y := by rw [heq]; exact hxmem
        exact (not_le_of_gt hyx) this
    exact Set.ncard_lt_ncard hss (Set.toFinite _)
  have key : ∀ n : ℕ, ∀ x : P, (Set.Iic x).ncard = n → α x = β x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      have hagree : ∀ y : P, y < x → α y = β y := by
        intro y hy
        exact ih (Set.Iic y).ncard (by rw [← hx]; exact hcard_lt x y hy) y rfl
      let C : Set Q := α '' (Set.Iic x \ {x})
      have hCcard : C.ncard = (Set.Iic x \ {x}).ncard := by
        exact Set.ncard_image_of_injective _ hα.injective
      have hdiffcard : (Set.Iic x \ {x}).ncard + 1 = (Set.Iic x).ncard := by
        exact Set.ncard_sdiff_singleton_add_one (by simp)
      have hTcard : (Set.Iic (β x)).ncard = (Set.Iic x).ncard := by
        rw [← h_down x]
        exact Set.ncard_image_of_injective _ hα.injective
      have hCcardT : C.ncard + 1 = (Set.Iic (β x)).ncard := by
        rw [hCcard, hdiffcard, hTcard]
      have hβx_notinC : β x ∉ C := by
        rintro ⟨y, hy, hαy⟩
        have hyne : y ≠ x := by
          simpa using hy.2
        have hyx : y < x := lt_of_le_of_ne hy.1 hyne
        have hαeqβ : α y = β y := hagree y hyx
        have : y = x := hβ.injective (by rw [← hαeqβ, hαy])
        exact hyne this
      have hCsubT : C ⊆ Set.Iic (β x) := by
        rintro q ⟨y, hy, rfl⟩
        have : α y ∈ α '' Set.Iic x := ⟨y, hy.1, rfl⟩
        rwa [h_down x] at this
      have hsub : C ∪ {β x} ⊆ Set.Iic (β x) := by
        intro q hq
        rcases hq with hq | hq
        · exact hCsubT hq
        · rw [Set.mem_singleton_iff] at hq
          rw [hq]
          exact le_rfl
      have hdisj : Disjoint C ({β x} : Set Q) := by
        rw [Set.disjoint_singleton_right]
        exact hβx_notinC
      have hunioncard : (C ∪ {β x}).ncard = C.ncard + 1 := by
        rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), Set.ncard_singleton]
      have hT_eq : Set.Iic (β x) = C ∪ {β x} := by
        refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
        rw [hunioncard, hCcardT]
      have hαx_inT : α x ∈ Set.Iic (β x) := by
        rw [← h_down x]
        exact ⟨x, le_rfl, rfl⟩
      have hαx_notinC : α x ∉ C := by
        rintro ⟨y, hy, hαy⟩
        have hyne : y ≠ x := by
          simpa using hy.2
        exact hyne (hα.injective hαy)
      have hαx_in_union : α x ∈ C ∪ {β x} := by
        rw [← hT_eq]
        exact hαx_inT
      rcases hαx_in_union with h | h
      · exact False.elim (hαx_notinC h)
      · simpa using h
  funext x
  exact key (Set.Iic x).ncard x rfl
