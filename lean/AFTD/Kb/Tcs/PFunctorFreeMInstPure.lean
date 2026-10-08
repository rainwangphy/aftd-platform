import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.CslibFreeMInstPure

/-!
# PFunctor.FreeM.instPure

Topic: algorithms   Node: b87db5147581

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.instPure`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.instPure
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
instance PFunctor.FreeM.instPure : Pure (P.FreeM) where pure := .pure
