import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeMInstLawfulMonad
import AFTD.Kb.Tcs.PFunctorFreeMLiftM
import AFTD.Kb.Tcs.PFunctorFreeMInstMonad
import AFTD.Kb.Tcs.PFunctorFreeMLiftMBind
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMLiftMLiftBind
import AFTD.Kb.Tcs.PFunctorFreeMLiftMMap
import AFTD.Kb.Tcs.PFunctorFreeMInstFunctor

/-!
# PFunctor.FreeM.liftM_seqLeft

Topic: algorithms   Node: 08f6e1b6d919

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.liftM_seqLeft`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.liftM_seqLeft
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
variable {m : Type uB → Type v} {α : Type uB} in
variable [Monad m] (interp : (a : P.A) → m (P.B a)) in
variable [LawfulMonad m] in
@[simp]
lemma PFunctor.FreeM.liftM_seqLeft {α β : Type uB}
    (interp : (a : P.A) → m (P.B a)) (x : P.FreeM α) (y : P.FreeM β) :
    (x <* y).liftM interp = x.liftM interp <* y.liftM interp := by
  simp [seqLeft_eq_bind]
