import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeM
import AFTD.Kb.Tcs.CslibFreeMStateF
import AFTD.Kb.Tcs.CslibFreeMFreeState
import AFTD.Kb.Tcs.CslibFreeMPureEqPure
import AFTD.Kb.Tcs.CslibFreeMBindEqBind
import AFTD.Kb.Tcs.CslibFreeMMapEqMap
import AFTD.Kb.Tcs.CslibFreeMLiftBindEq
import AFTD.Kb.Tcs.CslibFreeMPureBind
import AFTD.Kb.Tcs.CslibFreeMBindPure
import AFTD.Kb.Tcs.CslibFreeMBindPureComp
import AFTD.Kb.Tcs.CslibFreeMMapPure
import AFTD.Kb.Tcs.CslibFreeMMapBind
import AFTD.Kb.Tcs.CslibFreeMIdMap
import AFTD.Kb.Tcs.CslibFreeMLiftMPure
import AFTD.Kb.Tcs.CslibFreeMLiftMLiftBind
import AFTD.Kb.Tcs.CslibFreeMLiftMLift
import AFTD.Kb.Tcs.CslibFreeMLiftMBind
import AFTD.Kb.Tcs.CslibFreeMLiftMMap
import AFTD.Kb.Tcs.CslibFreeMLiftMSeq
import AFTD.Kb.Tcs.CslibFreeMLiftMSeqLeft
import AFTD.Kb.Tcs.CslibFreeMLiftMSeqRight
import AFTD.Kb.Tcs.CslibFreeMFreeStateGetDef
import AFTD.Kb.Tcs.CslibFreeMFreeStateSetDef
import AFTD.Kb.Tcs.CslibFreeMFreeStateStateInterp
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMInstFunctor
import AFTD.Kb.Tcs.CslibFreeMInstLawfulFunctor
import AFTD.Kb.Tcs.CslibFreeMInstMonad
import AFTD.Kb.Tcs.CslibFreeMInstLawfulMonad
import AFTD.Kb.Tcs.CslibFreeMFreeStateInstMonadStateOf

/-!
# Cslib.FreeM.FreeState.run

Topic: computability   Node: f5f159d13abe

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.FreeState.run`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Effects.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Run a state computation, returning both the result and final state.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
variable {σ : Type u} {α : Type v} in
/-- Run a state computation, returning both the result and final state. -/
def Cslib.FreeM.FreeState.run (comp : FreeState σ α) (s₀ : σ) : α × σ :=
  match comp with
  | .pure a => (a, s₀)
  | .liftBind StateF.get k => run (k s₀) s₀
  | .liftBind (StateF.set s') k => run (k PUnit.unit) s'
