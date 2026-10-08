import AFTD.Prelude
import AFTD.Kb.Tcs.CslibSKI
import AFTD.Kb.Tcs.CslibSKICoeTermPolynomial

/-!
# Cslib.SKI.One

Topic: computability   Node: 33f84992be18

Provenance: formalization of a published result. Source: CSLib, `Cslib.SKI.One`. Lean proof by Thomas Waring, Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CombinatoryLogic/Recursion.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Church one := λ f x. f x
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Church one := λ f x. f x -/
protected def Cslib.SKI.One : SKI := I
