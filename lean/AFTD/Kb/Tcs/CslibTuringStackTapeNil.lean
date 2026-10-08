import AFTD.Prelude
import AFTD.Kb.Tcs.CslibTuringStackTape

/-!
# Cslib.Turing.StackTape.nil

Topic: algorithms   Node: 6eb8314b4e95

Provenance: formalization of a published result. Source: CSLib, `Cslib.Turing.StackTape.nil`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/StackTape.lean (Copyright (c) 2026 Bolton Bailey. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The empty `StackTape`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.Turing in
attribute [local grind! .] StackTape.toList_getLast?_ne_some_none in
variable {Symbol : Type*} in
/-- The empty `StackTape` -/
def Cslib.Turing.StackTape.nil : StackTape Symbol := ⟨[], by grind⟩
