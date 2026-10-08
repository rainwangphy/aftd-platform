import AFTD.Prelude
import AFTD.Kb.Tcs.CslibSKI
import AFTD.Kb.Tcs.CslibSKIChurch
import AFTD.Kb.Tcs.CslibSKICoeTermPolynomial

/-!
# Cslib.SKI.Church_zero

Topic: computability   Node: ee7615e41593

Provenance: formalization of a published result. Source: CSLib, `Cslib.SKI.Church_zero`. Lean proof by Thomas Waring, Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CombinatoryLogic/Recursion.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.SKI.Church_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp] lemma Cslib.SKI.Church_zero (f x : SKI) : Church 0 f x = x := rfl
