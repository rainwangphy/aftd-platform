import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeMPureEqPure

/-!
# PFunctor.FreeM.pure_eq_pure

Topic: algorithms   Node: 259e3fb07a0f

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.pure_eq_pure`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.pure_eq_pure
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
@[simp]
theorem PFunctor.FreeM.pure_eq_pure : (FreeM.pure : α → P.FreeM α) = pure := rfl
