import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMBind
import AFTD.Kb.Tcs.PFunctorFreeMInstBind
import AFTD.Kb.Tcs.CslibFreeMBind
import AFTD.Kb.Tcs.CslibFreeMBindEqBind

/-!
# PFunctor.FreeM.bind_eq_bind

Topic: algorithms   Node: 00af486e63dd

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.bind_eq_bind`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Note that this lemma does not always apply, as it is universe-constrained by `Bind.bind`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
/-- Note that this lemma does not always apply, as it is universe-constrained by `Bind.bind`. -/
@[simp]
theorem PFunctor.FreeM.bind_eq_bind {α β : Type v} :
    (FreeM.bind : P.FreeM α → _ → P.FreeM β) = Bind.bind := rfl
