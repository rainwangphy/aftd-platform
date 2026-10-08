import AFTD.Prelude
import AFTD.Kb.Tcs.CslibTuringBiTape
import AFTD.Kb.Tcs.CslibTuringStackTape
import AFTD.Kb.Tcs.CslibTuringStackTapeInstEmptyCollection
import AFTD.Kb.Tcs.CslibTuringStackTapeMapSome
import AFTD.Kb.Tcs.CslibTuringBiTapeInstEmptyCollection
import AFTD.Kb.Tcs.CslibTuringStackTapeEmptyEqNil
import AFTD.Kb.Tcs.CslibTuringStackTapeNilToList
import AFTD.Kb.Tcs.CslibTuringStackTapeConsNoneNilToList
import AFTD.Kb.Tcs.CslibTuringStackTapeConsSomeToList
import AFTD.Kb.Tcs.CslibTuringStackTapeHeadCons
import AFTD.Kb.Tcs.CslibTuringStackTapeTailCons
import AFTD.Kb.Tcs.CslibTuringStackTapeConsHeadTail
import AFTD.Kb.Tcs.CslibTuringStackTapeLengthMapSome
import AFTD.Kb.Tcs.CslibTuringStackTapeLengthNil
import AFTD.Kb.Tcs.CslibTuringBiTapeEmptyEqNil
import AFTD.Kb.Tcs.CslibTuringStackTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringBiTapeInstInhabited

/-!
# Cslib.Turing.BiTape.mk₁

Topic: algorithms   Node: 905a60bf167d

Provenance: formalization of a published result. Source: CSLib, `Cslib.Turing.BiTape.mk₁`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/BiTape.lean (Copyright (c) 2026 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a `List` of `Symbol`s, construct a `BiTape` by mapping the list to `some` elements and laying them out to the right side, with the head under the first element of the list if it exists.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Turing Cslib.Turing.BiTape in
variable {Symbol : Type*} in
/-- Given a `List` of `Symbol`s, construct a `BiTape` by mapping the list to `some` elements and laying them out to the right side, with the head under the first element of the list if it exists. -/
def Cslib.Turing.BiTape.mk₁ (l : List Symbol) : BiTape Symbol :=
  match l with
  | [] => ∅
  | h :: t => { head := some h, left := ∅, right := StackTape.mapSome t }
