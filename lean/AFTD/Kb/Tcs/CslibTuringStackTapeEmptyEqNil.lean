import AFTD.Prelude
import AFTD.Kb.Tcs.CslibTuringStackTape
import AFTD.Kb.Tcs.CslibTuringStackTapeInstEmptyCollection
import AFTD.Kb.Tcs.CslibTuringStackTapeNil
import AFTD.Kb.Tcs.CslibTuringStackTapeInstInhabited

/-!
# Cslib.Turing.StackTape.empty_eq_nil

Topic: algorithms   Node: 223d5b6ef9c2

Provenance: formalization of a published result. Source: CSLib, `Cslib.Turing.StackTape.empty_eq_nil`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/StackTape.lean (Copyright (c) 2026 Bolton Bailey. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Cslib.Turing.StackTape.empty_eq_nil
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Turing Cslib.Turing.StackTape in
attribute [local grind! .] StackTape.toList_getLast?_ne_some_none in
variable {Symbol : Type*} in
@[simp]
lemma Cslib.Turing.StackTape.empty_eq_nil : (∅ : StackTape Symbol) = nil := rfl
