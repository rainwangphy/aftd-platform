import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMInstPure
import AFTD.Kb.Tcs.PFunctorFreeMLift
import AFTD.Kb.Tcs.PFunctorFreeMLiftNePure

/-!
# PFunctor.FreeM.pure_ne_lift

Topic: algorithms   Node: 1d380b1c47d5

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.pure_ne_lift`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.pure_ne_lift
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
@[simp] lemma PFunctor.FreeM.pure_ne_lift (a : P.A) (y : P.B a) :
    pure y ≠ (lift a : P.FreeM (P.B a)) := by simp [lift]
