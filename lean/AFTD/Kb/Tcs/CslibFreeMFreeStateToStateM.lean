import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeMFreeState
import AFTD.Kb.Tcs.CslibFreeMLiftM
import AFTD.Kb.Tcs.CslibFreeMStateF
import AFTD.Kb.Tcs.CslibFreeMFreeStateStateInterp
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
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMInstFunctor
import AFTD.Kb.Tcs.CslibFreeMInstLawfulFunctor
import AFTD.Kb.Tcs.CslibFreeMInstMonad
import AFTD.Kb.Tcs.CslibFreeMInstLawfulMonad
import AFTD.Kb.Tcs.CslibFreeMFreeStateInstMonadStateOf
import AFTD.Kb.Tcs.CslibFreeM
import AFTD.Kb.Tcs.PFunctorFreeMLiftM

/-!
# Cslib.FreeM.FreeState.toStateM

Topic: computability   Node: 022faa1b631b

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.FreeState.toStateM`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Effects.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Convert a `FreeState` computation into a `StateM` computation. This is the canonical interpreter derived from `liftM`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
variable {σ : Type u} {α : Type v} in
/-- Convert a `FreeState` computation into a `StateM` computation. This is the canonical interpreter derived from `liftM`. -/
abbrev Cslib.FreeM.FreeState.toStateM {α : Type u} (comp : FreeState σ α) : StateM σ α :=
  comp.liftM stateInterp
