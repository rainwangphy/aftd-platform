import AFTD.Prelude

/-!
# poset_height_two

Topic: combinatorics   Node: 61c3d0f6e42b

Provenance: formalization of a published result. Source: arXiv:2610.24774 Section 1

A poset has height two when it contains no chain of three elements.
-/

/-- A poset has height two if it contains no chain of three elements. -/
def poset_height_two (P : Type*) [PartialOrder P] : Prop := ∀ a b c : P, ¬ (a < b ∧ b < c)
