import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeMPureNeLift
import AFTD.Kb.Tcs.PFunctorFreeMLiftObj
import AFTD.Kb.Tcs.PFunctorFreeMMapEqMap
import AFTD.Kb.Tcs.PFunctorFreeMLiftBindEq
import AFTD.Kb.Tcs.PFunctorFreeMLiftNePure
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMInstPure
import AFTD.Kb.Tcs.PFunctorFreeMMap
import AFTD.Kb.Tcs.PFunctorFreeMBindPureComp

/-!
# PFunctor.FreeM.liftObj_ne_pure

Topic: algorithms   Node: 2cc2cef1717c

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.liftObj_ne_pure`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.liftObj_ne_pure
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
@[simp] lemma PFunctor.FreeM.liftObj_ne_pure (x : P.Obj α) (y : α) :
    (liftObj x : P.FreeM α) ≠ pure y := by simp [liftObj, lift, map, -liftBind_eq]
