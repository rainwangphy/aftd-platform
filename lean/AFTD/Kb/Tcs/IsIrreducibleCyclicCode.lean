import AFTD.Prelude
import AFTD.Kb.Tcs.IsCyclicCode

/-!
# is_irreducible_cyclic_code

Topic: information   Node: 2e9c4f24e3d3

Provenance: formalization of a published result. Source: arXiv:2610.28047 Definition 2.6

A cyclic code C of length n over a field F is irreducible if C is nonzero and every cyclic subcode C' ≤ C satisfies C' = ⊥ or C' = C.
-/

/-- A cyclic code is irreducible if it is nonzero and contains no proper non-trivial cyclic subcodes. -/
def is_irreducible_cyclic_code {F : Type*} [Field F] (n : ℕ) (C : Subspace F (Fin n → F)) : Prop := is_cyclic_code n C ∧ C ≠ ⊥ ∧
    ∀ C' : Subspace F (Fin n → F), C' ≤ C → is_cyclic_code n C' → C' = ⊥ ∨ C' = C
