import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.CslibFreeMLiftM

/-!
# PFunctor.FreeM.liftM

Topic: algorithms   Node: 1dfc63a95799

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.liftM`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Interpret a `FreeM P` computation into any monad `m` by providing an interpretation `interp : (a : P.A) → m (P.B a)` for each operation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
variable {m : Type uB → Type v} {α : Type uB} in
/-- Interpret a `FreeM P` computation into any monad `m` by providing an interpretation `interp : (a : P.A) → m (P.B a)` for each operation. -/
protected def PFunctor.FreeM.liftM [Pure m] [Bind m] (interp : (a : P.A) → m (P.B a)) : P.FreeM α → m α
  | .pure a => pure a
  | .liftBind a cont => interp a >>= fun u ↦ (cont u).liftM interp
