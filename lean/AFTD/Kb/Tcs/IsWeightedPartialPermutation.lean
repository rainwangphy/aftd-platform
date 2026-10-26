import AFTD.Prelude

/-!
# is_weighted_partial_permutation

Topic: combinatorics   Node: 9b401479106e

Provenance: formalization of a published result. Source: arXiv:2610.31807 Definition 3.12 and Theorem 3.13

A square complex matrix M is a weighted partial permutation matrix if for every row index i, any two column indices with nonzero entries are equal, and for every column index j, any two row indices with nonzero entries are equal.
-/

/-- A square matrix is a weighted partial permutation matrix if every row and column contains at most one nonzero entry. -/
def is_weighted_partial_permutation {n : Type*} (M : Matrix n n ℂ) : Prop := (∀ i, ∀ j₁ j₂, M i j₁ ≠ 0 → M i j₂ ≠ 0 → j₁ = j₂) ∧
  (∀ j, ∀ i₁ i₂, M i₁ j ≠ 0 → M i₂ j ≠ 0 → i₁ = i₂)
