import AFTD.Prelude

/-!
# Cslib.Logic.HasTensor

Topic: proof_theory   Node: 62667037c9df

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.HasTensor`. Lean proof by Fabrizio Montesi, Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Logic/Operators.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type `α` has a tensor connective (⊗).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The type `α` has a tensor connective (⊗). -/
class Cslib.Logic.HasTensor (α : Type*) where
  /-- `a ⊗ b` is the multiplicative conjunction of `a` and `b`. -/
  tensor (a b : α) : α
