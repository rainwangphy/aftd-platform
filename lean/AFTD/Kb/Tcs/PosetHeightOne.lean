import AFTD.Prelude

/-!
# poset_height_one

Topic: combinatorics   Node: 4eba0c967af1

Provenance: formalization of a published result. Source: arXiv:2610.12690 (Reconstruction of Finite Posets of Width Three), Sec. 9 (ordered sets of height one).

An ordered set has height one when its longest chains have exactly two elements: some two elements are comparable and there is no chain a < b < c.
-/

/-- An order of height one: some two elements are comparable, and there is no chain
`a < b < c`. -/
def poset_height_one (P : Type*) [PartialOrder P] : Prop :=
  (∃ a b : P, a < b) ∧ ∀ a b c : P, ¬ (a < b ∧ b < c)
