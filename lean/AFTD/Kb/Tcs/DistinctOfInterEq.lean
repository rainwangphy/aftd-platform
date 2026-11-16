import AFTD.Prelude

/-!
# distinct_of_inter_eq

Topic: combinatorics   Node: 2fd0105faaf1

Provenance: helper lemma. arXiv:2611.16957, Lemma 3.3 proof

Let V be a type with decidable equality, and let X₁, X₂, e₁, e₂ be finite sets (Finset V). If X₁ ⊆ e₁, X₂ ⊆ e₂, e₁ ∩ e₂ = X₁ ∩ X₂, and X₁ ≠ X₂, then e₁ ≠ e₂.
-/

/-- If e₁ = e₂, then e₁ = e₁ ∩ e₂ = X₁ ∩ X₂, forcing X₁ = e₁ = X₂, contradicting X₁ ≠ X₂. -/
theorem distinct_of_inter_eq {V : Type*} [DecidableEq V] {X₁ X₂ e₁ e₂ : Finset V} (h1 : X₁ ⊆ e₁) (h2 : X₂ ⊆ e₂) (hinter : e₁ ∩ e₂ = X₁ ∩ X₂) (hne : X₁ ≠ X₂) : e₁ ≠ e₂ := by
  intro he
  subst he
  have he1 : e₁ = X₁ ∩ X₂ := by
    rw [← hinter, Finset.inter_self]
  have hX1 : X₁ = e₁ := by
    apply Finset.Subset.antisymm h1
    rw [he1]
    exact Finset.inter_subset_left
  have hX2 : X₂ = e₁ := by
    apply Finset.Subset.antisymm h2
    rw [he1]
    exact Finset.inter_subset_right
  exact hne (hX1.trans hX2.symm)
