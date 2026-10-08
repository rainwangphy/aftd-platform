import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeMBindEqBind
import AFTD.Kb.Tcs.CslibFreeMPureBind
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMInstPure
import AFTD.Kb.Tcs.PFunctorFreeMBind

/-!
# PFunctor.FreeM.pure_bind

Topic: algorithms   Node: 60b2dd786b5e

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.pure_bind`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`.pure a` followed by `bind` collapses immediately.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
/-- `.pure a` followed by `bind` collapses immediately. -/
@[simp]
lemma PFunctor.FreeM.pure_bind (a : α) (f : α → P.FreeM β) :
    (pure a : P.FreeM α).bind f = f a := rfl
