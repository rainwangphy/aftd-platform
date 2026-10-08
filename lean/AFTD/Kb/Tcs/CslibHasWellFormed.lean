import AFTD.Prelude

/-!
# Cslib.HasWellFormed

Topic: computability   Node: 03939976d06b

Provenance: formalization of a published result. Source: CSLib, `Cslib.HasWellFormed`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Syntax/HasWellFormed.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Typeclass for types equipped with a well-formedness predicate.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Typeclass for types equipped with a well-formedness predicate. -/
class Cslib.HasWellFormed (α : Type u) where
  /-- Establishes whether `x` is well-formed. -/
  wf (x : α) : Prop
