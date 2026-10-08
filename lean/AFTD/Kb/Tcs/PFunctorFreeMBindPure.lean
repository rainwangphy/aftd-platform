import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeMBindEqBind
import AFTD.Kb.Tcs.CslibFreeMBindPure
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMInstPure
import AFTD.Kb.Tcs.PFunctorFreeMBind

/-!
# PFunctor.FreeM.bind_pure

Topic: algorithms   Node: a8366e682cb0

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.bind_pure`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.bind_pure
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
@[simp]
lemma PFunctor.FreeM.bind_pure : ∀ x : P.FreeM α, x.bind pure = x
  | .pure a => rfl
  | .liftBind a cont => by
    simp only [FreeM.bind]; congr 1; funext u; exact bind_pure (cont u)
