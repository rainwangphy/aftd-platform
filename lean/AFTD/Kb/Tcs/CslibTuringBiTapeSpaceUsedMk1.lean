import AFTD.Prelude
import AFTD.Kb.Tcs.CslibTuringBiTapeSpaceUsed
import AFTD.Kb.Tcs.CslibTuringBiTapeMk1
import AFTD.Kb.Tcs.CslibTuringStackTapeLength
import AFTD.Kb.Tcs.CslibTuringBiTape
import AFTD.Kb.Tcs.CslibTuringStackTapeLengthNil
import AFTD.Kb.Tcs.CslibTuringStackTapeLengthMapSome
import AFTD.Kb.Tcs.CslibTuringBiTapeNil
import AFTD.Kb.Tcs.CslibTuringStackTapeEmptyEqNil
import AFTD.Kb.Tcs.CslibTuringStackTapeNilToList
import AFTD.Kb.Tcs.CslibTuringStackTapeConsNoneNilToList
import AFTD.Kb.Tcs.CslibTuringStackTapeConsSomeToList
import AFTD.Kb.Tcs.CslibTuringStackTapeHeadCons
import AFTD.Kb.Tcs.CslibTuringStackTapeTailCons
import AFTD.Kb.Tcs.CslibTuringStackTapeConsHeadTail
import AFTD.Kb.Tcs.CslibTuringBiTapeEmptyEqNil
import AFTD.Kb.Tcs.CslibTuringBiTapeMoveLeftMoveRight
import AFTD.Kb.Tcs.CslibTuringBiTapeMoveRightMoveLeft
import AFTD.Kb.Tcs.CslibTuringBiTapeSpaceUsedWrite
import AFTD.Kb.Tcs.CslibTuringStackTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringStackTapeInstEmptyCollection
import AFTD.Kb.Tcs.CslibTuringBiTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringBiTapeInstEmptyCollection

/-!
# Cslib.Turing.BiTape.spaceUsed_mk₁

Topic: algorithms   Node: afc85cb4719b

Provenance: formalization of a published result. Source: CSLib, `Cslib.Turing.BiTape.spaceUsed_mk₁`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/BiTape.lean (Copyright (c) 2026 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.Turing.BiTape.spaceUsed_mk₁
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Turing Cslib.Turing.BiTape in
variable {Symbol : Type*} in
lemma Cslib.Turing.BiTape.spaceUsed_mk₁ (l : List Symbol) :
    (mk₁ l).spaceUsed = max 1 l.length := by
  cases l with
  | nil => simp [mk₁, spaceUsed, nil, StackTape.length_nil]
  | cons h t => simp [mk₁, spaceUsed, StackTape.length_nil, StackTape.length_mapSome]; omega
