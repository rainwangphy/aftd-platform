import AFTD.Prelude

/-!
# is_min_max_incomp_pair

Topic: combinatorics   Node: 89201000b3c6

Provenance: formalization of a published result. Source: arXiv:2610.24774 Section 1

A min-max incomparable pair (u, v) in a poset P consists of a minimal element u, a maximal element v, and u and v are incomparable.
-/

/-- A pair (u, v) is a min-max incomparable pair if u is minimal, v is maximal, and u and v are incomparable. -/
def is_min_max_incomp_pair {P : Type*} [PartialOrder P] (u v : P) : Prop := IsMin u ∧ IsMax v ∧ ¬ u ≤ v ∧ ¬ v ≤ u
