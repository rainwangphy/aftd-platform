import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMLiftM
import AFTD.Kb.Tcs.PFunctorFreeMInstBind
import AFTD.Kb.Tcs.PFunctorFreeMInduction
import AFTD.Kb.Tcs.PFunctorFreeMInstPure
import AFTD.Kb.Tcs.PFunctorFreeMInstMonad
import AFTD.Kb.Tcs.PFunctorFreeMInstLawfulMonad
import AFTD.Kb.Tcs.PFunctorFreeMBind
import AFTD.Kb.Tcs.PFunctorFreeMLift
import AFTD.Kb.Tcs.PFunctorFreeMLiftMLiftBind
import AFTD.Kb.Tcs.PFunctorFreeMBindEqBind
import AFTD.Kb.Tcs.PFunctorFreeMLiftMPure
import AFTD.Kb.Tcs.PFunctorFreeMLiftNePure
import AFTD.Kb.Tcs.PFunctorFreeMPureNeLift
import AFTD.Kb.Tcs.PFunctorFreeMLiftBindEq
import AFTD.Kb.Tcs.PFunctorFreeMBindPure
import AFTD.Kb.Tcs.PFunctorFreeMBindPureComp
import AFTD.Kb.Tcs.PFunctorFreeMLiftBindBind
import AFTD.Kb.Tcs.CslibFreeMBindAssoc
import AFTD.Kb.Tcs.CslibFreeMPureBind
import AFTD.Kb.Tcs.CslibFreeMLiftM

/-!
# PFunctor.FreeM.liftM_bind

Topic: algorithms   Node: 9ebd744d069e

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.liftM_bind`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.liftM_bind
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
variable {m : Type uB → Type v} {α : Type uB} in
variable [Monad m] (interp : (a : P.A) → m (P.B a)) in
variable [LawfulMonad m] in
@[simp]
lemma PFunctor.FreeM.liftM_bind {α β : Type uB} (x : P.FreeM α) (f : α → P.FreeM β) :
    (x >>= f).liftM interp = (do let u ← x.liftM interp; (f u).liftM interp) := by
  induction x with
  | pure _ => simp only [liftM_pure, LawfulMonad.pure_bind]
  | lift_bind a cont h =>
    simp_rw [bind_eq_bind]
    rw [LawfulMonad.bind_assoc, liftM_lift_bind]
    simp_rw [liftM_lift_bind, LawfulMonad.bind_assoc]
    congr 1
    funext u
    exact h u
