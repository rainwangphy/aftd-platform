import AFTD.Prelude
import AFTD.Kb.Tcs.CslibURMProgram
import AFTD.Kb.Tcs.CslibURMComputes
import AFTD.Kb.Tcs.CslibURMStateInstDecidableIsHalted
import AFTD.Kb.Tcs.CslibURMStateInstInhabited
import AFTD.Kb.Tcs.CslibURMStateInstRepr
import AFTD.Kb.Tcs.CslibURMInstSetoidProgram

/-!
# Cslib.URM.Computable

Topic: computability   Node: ade2fc1deae0

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Computable`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Computable.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A partial function `f : (Fin n → ℕ) → Part ℕ` is URM-computable if there exists a URM program that computes it.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A partial function `f : (Fin n → ℕ) → Part ℕ` is URM-computable if there exists a URM program that computes it. -/
def Cslib.URM.Computable (n : ℕ) (f : (Fin n → ℕ) → Part ℕ) : Prop :=
  ∃ p : Program, Computes n p f
