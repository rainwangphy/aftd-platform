import AFTD.Prelude

/-!
# booleanAffineRestriction

Topic: combinatorics   Node: f786967d7b50

Provenance: formalization of a published result. Source: arXiv:2611.03452, Lemma 2.2 and Section 2.4

The restriction of a Boolean function p to an affine subspace a + U is the function on Fin (dim U) → ZMod 2 obtained by evaluating p at a plus the linear combination of the canonical basis vectors of U.
-/

open scoped Pointwise in
/-- Restriction of a Boolean function p to the affine subspace a + U, represented as a function on Fin (dim U) -> ZMod 2 via the canonical basis of U. -/
noncomputable def booleanAffineRestriction {n : ℕ} (p : (Fin n → ZMod 2) → ZMod 2)
    (a : Fin n → ZMod 2) (U : Submodule (ZMod 2) (Fin n → ZMod 2)) :
    (Fin (Module.finrank (ZMod 2) U) → ZMod 2) → ZMod 2 := fun y => p (a + (Module.finBasis (ZMod 2) U).equivFun.symm y)
