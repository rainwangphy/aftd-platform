import AFTD.Prelude
import AFTD.Kb.Tcs.CslibSKI
import AFTD.Kb.Tcs.CslibSKICoeTermPolynomial

/-!
# Cslib.SKI.FF

Topic: computability   Node: 40490462bf03

Provenance: formalization of a published result. Source: CSLib, `Cslib.SKI.FF`. Lean proof by Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CombinatoryLogic/Basic.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Standard false: FF := λ x y. y
-/

open Cslib.SKI
@[inherit_doc]
local infixl:100 " ⬝ " => app

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relation in
/-- Standard false: FF := λ x y. y -/
def Cslib.SKI.FF : SKI := K ⬝ I
