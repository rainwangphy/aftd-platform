import AFTD.Prelude

/-!
# Cslib.Logic.HasOr

Topic: proof_theory   Node: b7140d7ae1b2

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.HasOr`. Lean proof by Fabrizio Montesi, Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Logic/Operators.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type `α` has an or connective (`∨`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The type `α` has an or connective (`∨`). -/
class Cslib.Logic.HasOr (α : Type*) where
  /-- `a ∨ b` is the disjunction of `a` and `b`. -/
  or (a b : α) : α
