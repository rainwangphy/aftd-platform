import AFTD.Prelude

/-!
# is_pure_mask

Topic: automata   Node: b3bdd80bb8b3

Provenance: formalization of a published result. Source: arXiv:2610.39941, Section 3

A binary mask is pure of value b if every element in the mask equals b.
-/

/-- A mask is pure if all its labels are identical to b. -/
def is_pure_mask (m : List Bool) (b : Bool) : Prop :=
  ∀ x ∈ m, x = b
