import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicShift

/-!
# is_cyclic_code

Topic: information   Node: 45255ee9809e

Provenance: formalization of a published result. Source: arXiv:2610.28047 Section 2.3

A subspace C of Fin n → F over a field F is a cyclic code if for every v in C, cyclic_shift n v is in C.
-/

/-- A subspace is a cyclic code if it is invariant under the cyclic coordinate shift. -/
def is_cyclic_code {F : Type*} [Field F] (n : ℕ) (C : Subspace F (Fin n → F)) : Prop := ∀ v ∈ C, cyclic_shift n v ∈ C
