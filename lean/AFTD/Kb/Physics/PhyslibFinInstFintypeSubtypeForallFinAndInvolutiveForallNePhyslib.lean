import AFTD.Prelude

/-!
# Physlib.Fin.instFintypeSubtypeForallFinAndInvolutiveForallNe_physlib

Topic: classical_mechanics   Node: 9defe79ce3b1

Provenance: formalization of a published result. Source: Physlib, `Physlib.Fin.instFintypeSubtypeForallFinAndInvolutiveForallNe_physlib`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type of fixed-point free involutions of `Fin n` is finite.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
/-- The type of fixed-point free involutions of `Fin n` is finite. -/
instance Physlib.Fin.instFintypeSubtypeForallFinAndInvolutiveForallNe_physlib {n : ℕ} : Fintype { f // Function.Involutive f ∧ ∀ (i : Fin n), f i ≠ i } := by
  have : DecidablePred fun x ↦ Function.Involutive x :=
    fun f ↦ Fintype.decidableForallFintype (α := Fin n)
  exact Subtype.fintype ..
