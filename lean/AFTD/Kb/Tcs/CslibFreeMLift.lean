import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeM
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMInstFunctor
import AFTD.Kb.Tcs.F

/-!
# Cslib.FreeM.lift

Topic: computability   Node: e10088bf1c53

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.lift`. Lean proof by Tanner Duve, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lift an operation from the effect signature `F` into the `FreeM F` monad.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
variable {F : Type u → Type v} {ι : Type u} {α : Type w} {β : Type w'} {γ : Type w''} in
/-- Lift an operation from the effect signature `F` into the `FreeM F` monad. -/
def Cslib.FreeM.lift (op : F ι) : FreeM F ι :=
  .liftBind op pure
