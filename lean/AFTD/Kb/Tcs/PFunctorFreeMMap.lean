import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM

/-!
# PFunctor.FreeM.map

Topic: algorithms   Node: c9f8d6982751

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.map`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Map a function over a `FreeM` computation. The builtin `<$>` notation should be preferred when `α` and `β` are in the same universe.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
/-- Map a function over a `FreeM` computation. The builtin `<$>` notation should be preferred when `α` and `β` are in the same universe. -/
def PFunctor.FreeM.map (f : α → β) : P.FreeM α → P.FreeM β
  | .pure a => .pure (f a)
  | .liftBind a cont => .liftBind a fun u => FreeM.map f (cont u)
