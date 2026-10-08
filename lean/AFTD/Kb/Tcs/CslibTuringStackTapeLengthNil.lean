import AFTD.Prelude
import AFTD.Kb.Tcs.CslibTuringStackTapeLength
import AFTD.Kb.Tcs.CslibTuringStackTapeNil
import AFTD.Kb.Tcs.CslibTuringStackTape
import AFTD.Kb.Tcs.CslibTuringStackTapeEmptyEqNil
import AFTD.Kb.Tcs.CslibTuringStackTapeNilToList
import AFTD.Kb.Tcs.CslibTuringStackTapeConsNoneNilToList
import AFTD.Kb.Tcs.CslibTuringStackTapeConsSomeToList
import AFTD.Kb.Tcs.CslibTuringStackTapeHeadCons
import AFTD.Kb.Tcs.CslibTuringStackTapeTailCons
import AFTD.Kb.Tcs.CslibTuringStackTapeConsHeadTail
import AFTD.Kb.Tcs.CslibTuringStackTapeLengthMapSome
import AFTD.Kb.Tcs.CslibTuringStackTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringStackTapeInstEmptyCollection

/-!
# Cslib.Turing.StackTape.length_nil

Topic: algorithms   Node: 5939ef9059e1

Provenance: formalization of a published result. Source: CSLib, `Cslib.Turing.StackTape.length_nil`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/StackTape.lean (Copyright (c) 2026 Bolton Bailey. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Cslib.Turing.StackTape.length_nil
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Turing Cslib.Turing.StackTape in
attribute [local grind! .] StackTape.toList_getLast?_ne_some_none in
variable {Symbol : Type*} in
@[simp, grind =]
lemma Cslib.Turing.StackTape.length_nil : (nil : StackTape Symbol).length = 0 := by grind
