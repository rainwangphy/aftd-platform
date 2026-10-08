import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeMStateF

/-!
# Cslib.FreeM.FreeState.stateInterp

Topic: computability   Node: 33ca0e7e6752

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.FreeState.stateInterp`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Effects.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Interpret `StateF` operations into `StateM`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
variable {σ : Type u} {α : Type v} in
/-- Interpret `StateF` operations into `StateM`. -/
@[simp]
def Cslib.FreeM.FreeState.stateInterp {α : Type u} : StateF σ α → StateM σ α
  | .get => MonadStateOf.get
  | .set s => MonadStateOf.set s
