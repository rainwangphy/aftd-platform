import AFTD.Prelude
import AFTD.Kb.Tcs.CslibTuringStackTape
import AFTD.Kb.Tcs.CslibTuringStackTapeEmptyEqNil
import AFTD.Kb.Tcs.CslibTuringStackTapeNilToList
import AFTD.Kb.Tcs.CslibTuringStackTapeConsNoneNilToList
import AFTD.Kb.Tcs.CslibTuringStackTapeConsSomeToList
import AFTD.Kb.Tcs.CslibTuringStackTapeHeadCons
import AFTD.Kb.Tcs.CslibTuringStackTapeTailCons
import AFTD.Kb.Tcs.CslibTuringStackTapeConsHeadTail
import AFTD.Kb.Tcs.CslibTuringStackTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringStackTapeInstEmptyCollection

/-!
# Cslib.Turing.StackTape.mapSome

Topic: algorithms   Node: d3f1122705d6

Provenance: formalization of a published result. Source: CSLib, `Cslib.Turing.StackTape.mapSome`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/StackTape.lean (Copyright (c) 2026 Bolton Bailey. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Create a `StackTape` from a list by mapping all elements to `some`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Turing in
attribute [local grind! .] StackTape.toList_getLast?_ne_some_none in
variable {Symbol : Type*} in
/-- Create a `StackTape` from a list by mapping all elements to `some` -/
@[grind]
def Cslib.Turing.StackTape.mapSome (l : List Symbol) : StackTape Symbol := ⟨l.map some, by simp⟩
