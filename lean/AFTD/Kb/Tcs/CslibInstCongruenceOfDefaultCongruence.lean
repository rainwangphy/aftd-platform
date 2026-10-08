import AFTD.Prelude
import AFTD.Kb.Tcs.CslibDefaultCongruence
import AFTD.Kb.Tcs.CslibCongruence

/-!
# Cslib.instCongruenceOfDefaultCongruence

Topic: computability   Node: 8708b126c437

Provenance: formalization of a published result. Source: CSLib, `Cslib.instCongruenceOfDefaultCongruence`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Syntax/Congruence.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.instCongruenceOfDefaultCongruence
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[nolint unusedArguments]
instance Cslib.instCongruenceOfDefaultCongruence (α : Type*) (r : α → α → Prop) [DefaultCongruence α r] : Congruence r := ⟨⟩
