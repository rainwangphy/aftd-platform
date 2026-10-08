import AFTD.Prelude

/-!
# Cslib.DefaultCongruence

Topic: computability   Node: b9bfd95fea95

Provenance: formalization of a published result. Source: CSLib, `Cslib.DefaultCongruence`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Syntax/Congruence.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type `α` has a canonical congruence relation. This gives access to the `≡` notation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The type `α` has a canonical congruence relation. This gives access to the `≡` notation. -/
class Cslib.DefaultCongruence (α : Type*) (r : outParam (α → α → Prop))
