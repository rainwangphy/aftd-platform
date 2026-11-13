import AFTD.Prelude

/-!
# is_pls

Topic: combinatorics   Node: 46e5b78a506c

Provenance: formalization of a published result. Source: arXiv:2611.13961, Section 1

A partial Latin square of order n is an n × n array with entries from {0, ..., n-1} such that each entry appears at most once in each row and at most once in each column.
-/

/-- Predicate for a partial Latin square of order n. -/
def is_pls {n : ℕ} (L : Fin n → Fin n → Option (Fin n)) : Prop :=
  (∀ (r c₁ c₂ : Fin n) (x : Fin n), L r c₁ = some x → L r c₂ = some x → c₁ = c₂) ∧
  (∀ (r₁ r₂ c : Fin n) (x : Fin n), L r₁ c = some x → L r₂ c = some x → r₁ = r₂)
