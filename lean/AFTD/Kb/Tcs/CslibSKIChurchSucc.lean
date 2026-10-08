import AFTD.Prelude
import AFTD.Kb.Tcs.CslibSKI
import AFTD.Kb.Tcs.CslibSKIChurch
import AFTD.Kb.Tcs.CslibSKIChurchZero
import AFTD.Kb.Tcs.CslibSKICoeTermPolynomial

/-!
# Cslib.SKI.Church_succ

Topic: computability   Node: 0ef18f57d915

Provenance: formalization of a published result. Source: CSLib, `Cslib.SKI.Church_succ`. Lean proof by Thomas Waring, Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CombinatoryLogic/Recursion.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.SKI.Church_succ
-/

open Cslib.SKI
@[inherit_doc]
local infixl:100 " ⬝ " => app

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp] lemma Cslib.SKI.Church_succ (n : Nat) (f x : SKI) : Church (n+1) f x = f ⬝ Church n f x := rfl
