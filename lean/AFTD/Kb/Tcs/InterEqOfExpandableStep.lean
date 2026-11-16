import AFTD.Prelude

/-!
# inter_eq_of_expandable_step

Topic: combinatorics   Node: 87adc2309d01

Provenance: helper lemma. arXiv:2611.16957, Lemma 3.3 proof

Let V be a type with decidable equality, and let X₁, X₂, e₁, e₂ be finite sets (Finset V). If X₁ ⊆ e₁, X₂ ⊆ e₂, Disjoint e₁ (X₂ \ X₁), and Disjoint e₂ (e₁ \ X₂), then e₁ ∩ e₂ = X₁ ∩ X₂.
-/

/-- Two edges e₁, e₂ containing X₁, X₂ respectively have intersection X₁ ∩ X₂ if each avoids the remainder of the other set. -/
theorem inter_eq_of_expandable_step {V : Type*} [DecidableEq V] {X₁ X₂ e₁ e₂ : Finset V} (h1 : X₁ ⊆ e₁) (h2 : X₂ ⊆ e₂) (hd1 : Disjoint e₁ (X₂ \ X₁)) (hd2 : Disjoint e₂ (e₁ \ X₂)) : e₁ ∩ e₂ = X₁ ∩ X₂ := by
  ext x
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨he1, he2⟩
    have hx2 : x ∈ X₂ := by
      by_contra hnot
      have hmem : x ∈ e₁ \ X₂ := Finset.mem_sdiff.mpr ⟨he1, hnot⟩
      exact Finset.disjoint_left.mp hd2 he2 hmem
    have hx1 : x ∈ X₁ := by
      by_contra hnot
      have hmem : x ∈ X₂ \ X₁ := Finset.mem_sdiff.mpr ⟨hx2, hnot⟩
      exact Finset.disjoint_left.mp hd1 he1 hmem
    exact ⟨hx1, hx2⟩
  · rintro ⟨hx1, hx2⟩
    exact ⟨h1 hx1, h2 hx2⟩
