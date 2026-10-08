import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeMInstLawfulMonad
import AFTD.Kb.Tcs.PFunctorFreeMLiftM
import AFTD.Kb.Tcs.PFunctorFreeMInstMonad
import AFTD.Kb.Tcs.PFunctorFreeMLiftMBind
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMLiftMLiftBind
import AFTD.Kb.Tcs.CslibFreeMBindPureComp
import AFTD.Kb.Tcs.PFunctorFreeMLiftMPure
import AFTD.Kb.Tcs.PFunctorFreeMInstFunctor

/-!
# PFunctor.FreeM.liftM_map

Topic: algorithms   Node: e67d57bb1739

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.liftM_map`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.liftM_map
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
variable {m : Type uB → Type v} {α : Type uB} in
variable [Monad m] (interp : (a : P.A) → m (P.B a)) in
variable [LawfulMonad m] in
@[simp]
lemma PFunctor.FreeM.liftM_map {α β : Type uB} (f : α → β) (x : P.FreeM α) :
    (f <$> x).liftM interp = f <$> x.liftM interp := by
  simp_rw [← LawfulMonad.bind_pure_comp, liftM_bind, liftM_pure]
