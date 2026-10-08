import AFTD.Prelude

/-!
# Cslib.Logic.HasNot

Topic: proof_theory   Node: 5a381db3ba90

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.HasNot`. Lean proof by Fabrizio Montesi, Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Logic/Operators.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type `α` has a negation connective (`¬`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The type `α` has a negation connective (`¬`). -/
class Cslib.Logic.HasNot (α : Type*) where
  /-- `¬a` is the negation of `a`. -/
  not (a : α) : α
