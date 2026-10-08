import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMInstMonadLiftObj
import AFTD.Kb.Tcs.PFunctorFreeMLiftObj
import AFTD.Kb.Tcs.PFunctorFreeMLiftNePure
import AFTD.Kb.Tcs.PFunctorFreeMPureNeLift
import AFTD.Kb.Tcs.PFunctorFreeMMapEqMap
import AFTD.Kb.Tcs.PFunctorFreeMLiftBindEq
import AFTD.Kb.Tcs.PFunctorFreeMLiftObjNePure
import AFTD.Kb.Tcs.PFunctorFreeMPureNeLiftObj

/-!
# PFunctor.FreeM.monadLift_eq_liftObj

Topic: algorithms   Node: 2fbcc93c276a

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.monadLift_eq_liftObj`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.monadLift_eq_liftObj
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
lemma PFunctor.FreeM.monadLift_eq_liftObj (x : P.Obj α) : (x : P.FreeM α) = FreeM.liftObj x := rfl
