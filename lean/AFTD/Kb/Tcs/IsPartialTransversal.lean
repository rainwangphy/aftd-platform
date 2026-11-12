import AFTD.Prelude

/-!
# is_partial_transversal

Topic: combinatorics   Node: f33f70659c99

Provenance: formalization of a published result. Source: arXiv:2611.13961, Section 2

Given a dimension δ : ℕ, an ambient finset of cells S in Fin δ × Fin δ, and a finset of cells T in Fin δ × Fin δ, is_partial_transversal S T asserts that T is a subset of S, and the coordinate projections from T to Fin δ are injective: for all p, q ∈ T, p.1 = q.1 implies p = q, and for all p, q ∈ T, p.2 = q.2 implies p = q.
-/

/-- A set of cells T is a partial transversal of S if T ⊆ S and no two cells share a row or column. -/
def is_partial_transversal {δ : ℕ} (S : Finset (Fin δ × Fin δ)) (T : Finset (Fin δ × Fin δ)) : Prop :=
  T ⊆ S ∧ (∀ p ∈ T, ∀ q ∈ T, p.1 = q.1 → p = q) ∧ (∀ p ∈ T, ∀ q ∈ T, p.2 = q.2 → p = q)
