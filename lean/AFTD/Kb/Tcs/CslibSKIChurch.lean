import AFTD.Prelude
import AFTD.Kb.Tcs.CslibSKI
import AFTD.Kb.Tcs.CslibSKICoeTermPolynomial

/-!
# Cslib.SKI.Church

Topic: computability   Node: 2cddb42bc67e

Provenance: formalization of a published result. Source: CSLib, `Cslib.SKI.Church`. Lean proof by Thomas Waring, Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CombinatoryLogic/Recursion.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Function form of the church numerals.
-/

open Cslib.SKI
@[inherit_doc]
local infixl:100 " ⬝ " => app

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Function form of the church numerals. -/
def Cslib.SKI.Church (n : Nat) (f x : SKI) : SKI :=
match n with
| 0 => x
| n+1 => f ⬝ (Church n f x)
