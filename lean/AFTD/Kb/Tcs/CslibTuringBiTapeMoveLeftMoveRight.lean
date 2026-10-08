import AFTD.Prelude
import AFTD.Kb.Tcs.CslibTuringBiTape
import AFTD.Kb.Tcs.CslibTuringBiTapeMoveRight
import AFTD.Kb.Tcs.CslibTuringBiTapeMoveLeft
import AFTD.Kb.Tcs.CslibTuringStackTape
import AFTD.Kb.Tcs.CslibTuringStackTapeHead
import AFTD.Kb.Tcs.CslibTuringStackTapeCons
import AFTD.Kb.Tcs.CslibTuringStackTapeTail
import AFTD.Kb.Tcs.CslibTuringStackTapeHeadCons
import AFTD.Kb.Tcs.CslibTuringStackTapeConsHeadTail
import AFTD.Kb.Tcs.CslibTuringStackTapeTailCons
import AFTD.Kb.Tcs.CslibTuringStackTapeEmptyEqNil
import AFTD.Kb.Tcs.CslibTuringStackTapeNilToList
import AFTD.Kb.Tcs.CslibTuringStackTapeConsNoneNilToList
import AFTD.Kb.Tcs.CslibTuringStackTapeConsSomeToList
import AFTD.Kb.Tcs.CslibTuringStackTapeLengthMapSome
import AFTD.Kb.Tcs.CslibTuringStackTapeLengthNil
import AFTD.Kb.Tcs.CslibTuringBiTapeEmptyEqNil
import AFTD.Kb.Tcs.CslibTuringStackTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringStackTapeInstEmptyCollection
import AFTD.Kb.Tcs.CslibTuringBiTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringBiTapeInstEmptyCollection

/-!
# Cslib.Turing.BiTape.moveLeft_moveRight

Topic: algorithms   Node: 641bc35aabeb

Provenance: formalization of a published result. Source: CSLib, `Cslib.Turing.BiTape.moveLeft_moveRight`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/BiTape.lean (Copyright (c) 2026 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Turing.BiTape.moveLeft_moveRight
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Turing Cslib.Turing.BiTape in
variable {Symbol : Type*} in
open _root_.Turing in
@[simp]
lemma Cslib.Turing.BiTape.moveLeft_moveRight (t : BiTape Symbol) : t.moveLeft.moveRight = t := by
  simp [moveRight, moveLeft]
