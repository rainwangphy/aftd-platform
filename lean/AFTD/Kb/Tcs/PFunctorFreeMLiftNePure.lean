import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMLift
import AFTD.Kb.Tcs.PFunctorFreeMInstPure

/-!
# PFunctor.FreeM.lift_ne_pure

Topic: algorithms   Node: a9d3c998b4b5

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.lift_ne_pure`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.lift_ne_pure
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
@[simp] lemma PFunctor.FreeM.lift_ne_pure (a : P.A) (y : P.B a) :
    (lift a : P.FreeM (P.B a)) ≠ pure y := by simp [lift]
