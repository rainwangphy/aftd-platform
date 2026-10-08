import AFTD.Prelude
import AFTD.Kb.Tcs.CslibSKI
import AFTD.Kb.Tcs.CslibSKIChurchZero
import AFTD.Kb.Tcs.CslibSKIChurchSucc
import AFTD.Kb.Tcs.CslibSKICoeTermPolynomial

/-!
# Cslib.SKI.Zero

Topic: computability   Node: c45f726a086a

Provenance: formalization of a published result. Source: CSLib, `Cslib.SKI.Zero`. Lean proof by Thomas Waring, Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CombinatoryLogic/Recursion.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Church zero := λ f x. x
-/

open Cslib.SKI
@[inherit_doc]
local infixl:100 " ⬝ " => app

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Church zero := λ f x. x -/
protected def Cslib.SKI.Zero : SKI := K ⬝ I
