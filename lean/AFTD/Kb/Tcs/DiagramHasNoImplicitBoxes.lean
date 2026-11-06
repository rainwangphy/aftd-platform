import AFTD.Prelude

/-!
# diagram_has_no_implicit_boxes

Topic: combinatorics   Node: 4507c84bb5bf

Provenance: formalization of a published result. Source: arXiv:2611.07715 Definition 2.1

A finite diagram D in ℕ² has no implicit boxes if whenever two cells of D lie in the same row (respectively, column), every cell between them in that row (respectively, column) also belongs to D.
-/

/-- A diagram D has no implicit boxes if it is closed under filling gaps within any row or column. -/
def diagram_has_no_implicit_boxes (D : Finset (ℕ × ℕ)) : Prop := (∀ i j₁ j₂ j, (i, j₁) ∈ D → (i, j₂) ∈ D → j₁ ≤ j → j ≤ j₂ → (i, j) ∈ D) ∧
   (∀ i₁ i₂ j i, (i₁, j) ∈ D → (i₂, j) ∈ D → i₁ ≤ i → i ≤ i₂ → (i, j) ∈ D)
