import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeMBindEqBind
import AFTD.Kb.Tcs.PFunctorFreeMPureNeLift
import AFTD.Kb.Tcs.PFunctorFreeMLift
import AFTD.Kb.Tcs.PFunctorFreeMLiftBindEq
import AFTD.Kb.Tcs.PFunctorFreeMBindPure
import AFTD.Kb.Tcs.PFunctorFreeMLiftNePure
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.CslibFreeMBindAssoc
import AFTD.Kb.Tcs.PFunctorFreeMInstPure
import AFTD.Kb.Tcs.PFunctorFreeMBindPureComp
import AFTD.Kb.Tcs.PFunctorFreeMBindAssoc
import AFTD.Kb.Tcs.PFunctorFreeMBind

/-!
# PFunctor.FreeM.liftBind_bind

Topic: algorithms   Node: 4fa2b4e5b5bb

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.liftBind_bind`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.liftBind_bind
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
@[simp]
lemma PFunctor.FreeM.liftBind_bind (a : P.A) (cont : P.B a → P.FreeM β) (f : β → P.FreeM γ) :
    ((FreeM.lift a).bind cont).bind f = (FreeM.lift a).bind (fun u ↦ (cont u).bind f) := by
  simp only [lift]
  exact FreeM.bind_assoc (FreeM.liftBind a pure) cont f
