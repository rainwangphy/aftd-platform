import AFTD.Prelude

/-!
# Cslib.HasAlphaEquiv

Topic: computability   Node: 4cf8e7363ba7

Provenance: formalization of a published result. Source: CSLib, `Cslib.HasAlphaEquiv`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Syntax/HasAlphaEquiv.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Typeclass for the α-equivalence notation `x =α y`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Typeclass for the α-equivalence notation `x =α y`. -/
class Cslib.HasAlphaEquiv (β : Type u) where
  /-- α-equivalence relation for type β. -/
  AlphaEquiv : β → β → Prop
