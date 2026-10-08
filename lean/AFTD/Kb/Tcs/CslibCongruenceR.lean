import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCongruence

/-!
# Cslib.Congruence.r

Topic: computability   Node: cee36ba04151

Provenance: formalization of a published result. Source: CSLib, `Cslib.Congruence.r`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Syntax/Congruence.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`a ≡[r] b` means that the `a` and `b` are related by the congruence `r`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- `a ≡[r] b` means that the `a` and `b` are related by the congruence `r`. -/
@[nolint unusedArguments]
def Cslib.Congruence.r (r : α → α → Prop) [Congruence r] := r
