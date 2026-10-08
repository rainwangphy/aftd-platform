import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeMFreeState
import AFTD.Kb.Tcs.CslibFreeMFreeStateToStateM
import AFTD.Kb.Tcs.CslibFreeMFreeStateRun'
import AFTD.Kb.Tcs.CslibFreeMFreeStateRun
import AFTD.Kb.Tcs.CslibFreeMFreeStateRunToStateM
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
import AFTD.Kb.Tcs.CslibFreeMFreeStateRunPure
import AFTD.Kb.Tcs.CslibFreeMFreeStateRunGet
import AFTD.Kb.Tcs.CslibFreeMFreeStateRunSet
import AFTD.Kb.Tcs.CslibFreeMFreeStateRunBind
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMInstFunctor
import AFTD.Kb.Tcs.CslibFreeMInstLawfulFunctor
import AFTD.Kb.Tcs.CslibFreeMInstMonad
import AFTD.Kb.Tcs.CslibFreeMInstLawfulMonad
import AFTD.Kb.Tcs.CslibFreeMFreeStateInstMonadStateOf
import AFTD.Kb.Tcs.CslibFreeM

/-!
# Cslib.FreeM.FreeState.run'_toStateM

Topic: computability   Node: c4345c082dbe

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.FreeState.run'_toStateM`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Effects.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.FreeM.FreeState.run'_toStateM
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
variable {σ : Type u} {α : Type v} in
theorem Cslib.FreeM.FreeState.run'_toStateM {α : Type u} (comp : FreeState σ α) (s₀ : σ) :
    (toStateM comp).run' s₀ = pure (run' comp s₀) := by
  rw [run', StateT.run'_eq, run_toStateM]
  rfl
