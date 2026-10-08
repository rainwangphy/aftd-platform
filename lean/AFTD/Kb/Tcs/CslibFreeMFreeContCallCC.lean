import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeMFreeCont
import AFTD.Kb.Tcs.CslibFreeMLift
import AFTD.Kb.Tcs.CslibFreeMContF
import AFTD.Kb.Tcs.CslibFreeMFreeContRun
import AFTD.Kb.Tcs.CslibFreeM
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
import AFTD.Kb.Tcs.CslibFreeMFreeStateRunToStateM
import AFTD.Kb.Tcs.CslibFreeMFreeStateRunPure
import AFTD.Kb.Tcs.CslibFreeMFreeStateRunGet
import AFTD.Kb.Tcs.CslibFreeMFreeStateRunSet
import AFTD.Kb.Tcs.CslibFreeMFreeStateRunBind
import AFTD.Kb.Tcs.CslibFreeMFreeStateRun'Get
import AFTD.Kb.Tcs.CslibFreeMFreeStateRun'Set
import AFTD.Kb.Tcs.CslibFreeMFreeWriterRunPure
import AFTD.Kb.Tcs.CslibFreeMFreeWriterRunLiftTell
import AFTD.Kb.Tcs.CslibFreeMFreeWriterRunBind
import AFTD.Kb.Tcs.CslibFreeMFreeWriterRunToWriterT
import AFTD.Kb.Tcs.CslibFreeMFreeWriterListenLiftTellBind
import AFTD.Kb.Tcs.CslibFreeMFreeContContInterp
import AFTD.Kb.Tcs.CslibFreeMFreeContRunPure
import AFTD.Kb.Tcs.CslibFreeMFreeContRunLiftCallCC
import AFTD.Kb.Tcs.CslibFreeMFreeContRunBind
import AFTD.Kb.Tcs.CslibFreeMFreeContRunToContT
import AFTD.Kb.Tcs.CslibFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMInstFunctor
import AFTD.Kb.Tcs.CslibFreeMInstLawfulFunctor
import AFTD.Kb.Tcs.CslibFreeMInstMonad
import AFTD.Kb.Tcs.CslibFreeMInstLawfulMonad
import AFTD.Kb.Tcs.CslibFreeMInstFunctorContF

/-!
# Cslib.FreeM.FreeCont.callCC

Topic: computability   Node: bdb9809bc3a8

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.FreeCont.callCC`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Effects.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Call with current continuation for the Free continuation monad.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.FreeM Cslib.FreeM.FreeCont in
universe u v w w' w'' in
variable {r : Type u} {α : Type v} {β : Type w} in
/-- Call with current continuation for the Free continuation monad. -/
def Cslib.FreeM.FreeCont.callCC (f : MonadCont.Label α (FreeCont r) β → FreeCont r α) :
    FreeCont r α :=
  lift (.callCC fun k => run (f ⟨fun x => lift (.callCC fun _ => k x)⟩) k)
