import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeMLiftM
import AFTD.Kb.Tcs.PFunctorFreeMLift
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMInstBind
import AFTD.Kb.Tcs.PFunctorFreeMInstPure
import AFTD.Kb.Tcs.PFunctorFreeMInstMonad
import AFTD.Kb.Tcs.PFunctorFreeMInstLawfulMonad
import AFTD.Kb.Tcs.PFunctorFreeMLiftMLiftBind
import AFTD.Kb.Tcs.PFunctorFreeMBindPure
import AFTD.Kb.Tcs.PFunctorFreeMPureEqPure
import AFTD.Kb.Tcs.PFunctorFreeMLiftNePure
import AFTD.Kb.Tcs.PFunctorFreeMPureNeLift
import AFTD.Kb.Tcs.PFunctorFreeMBindEqBind
import AFTD.Kb.Tcs.PFunctorFreeMMapEqMap
import AFTD.Kb.Tcs.PFunctorFreeMLiftBindEq
import AFTD.Kb.Tcs.PFunctorFreeMLiftObjNePure
import AFTD.Kb.Tcs.PFunctorFreeMPureNeLiftObj
import AFTD.Kb.Tcs.PFunctorFreeMPureBind
import AFTD.Kb.Tcs.PFunctorFreeMBindPureComp
import AFTD.Kb.Tcs.PFunctorFreeMLiftBindBind
import AFTD.Kb.Tcs.PFunctorFreeMLiftObjBind
import AFTD.Kb.Tcs.PFunctorFreeMBindEqPureIff
import AFTD.Kb.Tcs.PFunctorFreeMPureEqBindIff
import AFTD.Kb.Tcs.PFunctorFreeMIdMap
import AFTD.Kb.Tcs.PFunctorFreeMPureInj
import AFTD.Kb.Tcs.PFunctorFreeMLiftMPure
import AFTD.Kb.Tcs.PFunctorFreeMLiftMBind
import AFTD.Kb.Tcs.PFunctorFreeMLiftMMap
import AFTD.Kb.Tcs.PFunctorFreeMLiftMSeq
import AFTD.Kb.Tcs.PFunctorFreeMLiftMSeqLeft
import AFTD.Kb.Tcs.PFunctorFreeMLiftMSeqRight
import AFTD.Kb.Tcs.CslibFreeMLift
import AFTD.Kb.Tcs.CslibFreeMLiftM

/-!
# PFunctor.FreeM.liftM_lift

Topic: algorithms   Node: 6ff9718571cb

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.liftM_lift`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.liftM_lift
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
variable {m : Type uB → Type v} {α : Type uB} in
variable [Monad m] (interp : (a : P.A) → m (P.B a)) in
variable [LawfulMonad m] in
@[simp]
lemma PFunctor.FreeM.liftM_lift (interp : (a : P.A) → m (P.B a)) (a : P.A) :
    (FreeM.lift a).liftM interp = interp a := by
  simpa [bind_pure] using
    (liftM_lift_bind (interp := interp) (a := a) (cont := pure))
