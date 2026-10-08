import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMBind
import AFTD.Kb.Tcs.PFunctorFreeMInduction
import AFTD.Kb.Tcs.PFunctorFreeMInstPure
import AFTD.Kb.Tcs.PFunctorFreeMLift
import AFTD.Kb.Tcs.PFunctorFreeMLiftBindEq
import AFTD.Kb.Tcs.PFunctorFreeMLiftNePure
import AFTD.Kb.Tcs.PFunctorFreeMPureNeLift
import AFTD.Kb.Tcs.PFunctorFreeMBindEqBind
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.CslibFreeMBind
import AFTD.Kb.Tcs.CslibFreeMBindAssoc

/-!
# PFunctor.FreeM.bind_assoc

Topic: algorithms   Node: d0b83e0e1c1f

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.bind_assoc`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.bind_assoc
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
protected theorem PFunctor.FreeM.bind_assoc (x : P.FreeM α) (f : α → P.FreeM β) (g : β → P.FreeM γ) :
    (x.bind f).bind g = x.bind (fun a => (f a).bind g) := by
  induction x with
  | pure a => rfl
  | lift_bind a cont ih => simp [← liftBind_eq, FreeM.bind, ih] at *
