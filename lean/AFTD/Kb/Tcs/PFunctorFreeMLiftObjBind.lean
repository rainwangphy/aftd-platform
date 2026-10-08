import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMBind
import AFTD.Kb.Tcs.PFunctorFreeMLiftObj
import AFTD.Kb.Tcs.PFunctorFreeMLiftNePure
import AFTD.Kb.Tcs.PFunctorFreeMPureNeLift
import AFTD.Kb.Tcs.PFunctorFreeMBindEqBind
import AFTD.Kb.Tcs.PFunctorFreeMMapEqMap
import AFTD.Kb.Tcs.PFunctorFreeMLiftBindEq
import AFTD.Kb.Tcs.PFunctorFreeMLiftObjNePure
import AFTD.Kb.Tcs.PFunctorFreeMPureNeLiftObj
import AFTD.Kb.Tcs.PFunctorFreeMBindPure
import AFTD.Kb.Tcs.PFunctorFreeMBindPureComp
import AFTD.Kb.Tcs.PFunctorFreeMLiftBindBind
import AFTD.Kb.Tcs.CslibFreeMBind

/-!
# PFunctor.FreeM.liftObj_bind

Topic: algorithms   Node: cee7671b0a6e

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.liftObj_bind`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.liftObj_bind
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
@[simp]
lemma PFunctor.FreeM.liftObj_bind (x : P.Obj α) (f : α → P.FreeM β) :
    (FreeM.liftObj x).bind f = FreeM.liftBind x.1 (fun a ↦ f (x.2 a)) := rfl
