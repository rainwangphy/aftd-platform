import AFTD.Prelude
import AFTD.Kb.Tcs.CslibDefaultCongruence

/-!
# Cslib.DefaultCongruence.r

Topic: computability   Node: 1a77a01e209a

Provenance: formalization of a published result. Source: CSLib, `Cslib.DefaultCongruence.r`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Syntax/Congruence.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`a ≡ b` means that `a` and `b` are related by the canonical congruence relation for their type.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- `a ≡ b` means that `a` and `b` are related by the canonical congruence relation for their type. -/
@[nolint unusedArguments]
def Cslib.DefaultCongruence.r {α : Type*} {r : α → α → Prop} [DefaultCongruence α r] (a b : α) := r a b
