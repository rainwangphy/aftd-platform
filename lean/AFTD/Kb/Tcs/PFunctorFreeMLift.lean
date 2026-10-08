import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMInstPure
import AFTD.Kb.Tcs.CslibFreeMLift

/-!
# PFunctor.FreeM.lift

Topic: algorithms   Node: 909ed9db5518

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.lift`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lift a shape of the base polynomial functor into the free monad.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
/-- Lift a shape of the base polynomial functor into the free monad. -/
def PFunctor.FreeM.lift (a : P.A) : P.FreeM (P.B a) := FreeM.liftBind a pure
