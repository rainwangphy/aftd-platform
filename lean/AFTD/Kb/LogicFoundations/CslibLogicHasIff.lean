import AFTD.Prelude

/-!
# Cslib.Logic.HasIff

Topic: proof_theory   Node: cf4d74ed116a

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.HasIff`. Lean proof by Fabrizio Montesi, Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Logic/Operators.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type `α` has a bi-implication connective (`↔`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The type `α` has a bi-implication connective (`↔`). -/
class Cslib.Logic.HasIff (α : Type*) where
  /-- `a ↔ b` denotes `a` implies `b` and vice-versa. -/
  iff (a b : α) : α
