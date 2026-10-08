import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.CslibFreeMBind

/-!
# PFunctor.FreeM.bind

Topic: algorithms   Node: d5b7cf580c88

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.bind`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Bind operation for the `FreeM` monad. The builtin `>>=` notation should be preferred when `α` and `β` are in the same universe.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
/-- Bind operation for the `FreeM` monad. The builtin `>>=` notation should be preferred when `α` and `β` are in the same universe. -/
protected def PFunctor.FreeM.bind : P.FreeM α → (α → P.FreeM β) → P.FreeM β
  | FreeM.pure a, f => f a
  | FreeM.liftBind a cont, f => FreeM.liftBind a (fun u ↦ FreeM.bind (cont u) f)
