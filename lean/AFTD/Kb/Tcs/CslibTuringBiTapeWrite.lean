import AFTD.Prelude
import AFTD.Kb.Tcs.CslibTuringBiTape
import AFTD.Kb.Tcs.CslibTuringBiTapeEmptyEqNil
import AFTD.Kb.Tcs.CslibTuringBiTapeMoveLeftMoveRight
import AFTD.Kb.Tcs.CslibTuringBiTapeMoveRightMoveLeft
import AFTD.Kb.Tcs.CslibTuringBiTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringBiTapeInstEmptyCollection

/-!
# Cslib.Turing.BiTape.write

Topic: algorithms   Node: 642fe74372e6

Provenance: formalization of a published result. Source: CSLib, `Cslib.Turing.BiTape.write`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/BiTape.lean (Copyright (c) 2026 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Write a value under the head of the `BiTape`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Turing in
variable {Symbol : Type*} in
/-- Write a value under the head of the `BiTape`. -/
def Cslib.Turing.BiTape.write (t : BiTape Symbol) (a : Option Symbol) : BiTape Symbol := { t with head := a }
