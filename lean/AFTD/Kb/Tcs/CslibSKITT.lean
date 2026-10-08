import AFTD.Prelude
import AFTD.Kb.Tcs.CslibSKI
import AFTD.Kb.Tcs.CslibSKICoeTermPolynomial

/-!
# Cslib.SKI.TT

Topic: computability   Node: 537a77072182

Provenance: formalization of a published result. Source: CSLib, `Cslib.SKI.TT`. Lean proof by Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CombinatoryLogic/Basic.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Standard true: TT := λ x y. x
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relation in
/-- Standard true: TT := λ x y. x -/
def Cslib.SKI.TT : SKI := K
