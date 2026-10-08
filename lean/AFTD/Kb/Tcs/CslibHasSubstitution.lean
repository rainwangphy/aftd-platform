import AFTD.Prelude

/-!
# Cslib.HasSubstitution

Topic: computability   Node: d375b7388a55

Provenance: formalization of a published result. Source: CSLib, `Cslib.HasSubstitution`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Syntax/HasSubstitution.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Typeclass for substitution relations and access to their notation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Typeclass for substitution relations and access to their notation. -/
class Cslib.HasSubstitution (α : Type u) (β : Type v) (γ : Type w) where
  /-- Substitution function. Replaces `x` in `t` with `t'`. -/
  subst (t : α) (x : β) (t' : γ) : α
