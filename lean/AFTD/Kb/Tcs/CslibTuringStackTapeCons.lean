import AFTD.Prelude
import AFTD.Kb.Tcs.CslibTuringStackTape
import AFTD.Kb.Tcs.CslibTuringStackTapeEmptyEqNil
import AFTD.Kb.Tcs.CslibTuringStackTapeNilToList
import AFTD.Kb.Tcs.CslibTuringStackTapeInstInhabited
import AFTD.Kb.Tcs.CslibTuringStackTapeInstEmptyCollection

/-!
# Cslib.Turing.StackTape.cons

Topic: algorithms   Node: 70810a588f9d

Provenance: formalization of a published result. Source: CSLib, `Cslib.Turing.StackTape.cons`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/StackTape.lean (Copyright (c) 2026 Bolton Bailey. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Prepend an `Option` to the `StackTape`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Turing in
attribute [local grind! .] StackTape.toList_getLast?_ne_some_none in
variable {Symbol : Type*} in
/-- Prepend an `Option` to the `StackTape` -/
def Cslib.Turing.StackTape.cons (x : Option Symbol) (xs : StackTape Symbol) : StackTape Symbol :=
  match x, xs with
  | none, ⟨[], _⟩ => ⟨[], by grind⟩
  | none, ⟨hd :: tl, hl⟩ => ⟨none :: hd :: tl, by grind⟩
  | some a, ⟨l, hl⟩ => ⟨some a :: l, by grind⟩
