import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMMap
import AFTD.Kb.Tcs.CslibFreeMMap
import AFTD.Kb.Tcs.CslibFreeMInstFunctor

/-!
# PFunctor.FreeM.instFunctor

Topic: algorithms   Node: ff582c1cf52e

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.instFunctor`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.instFunctor
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
instance PFunctor.FreeM.instFunctor : Functor (P.FreeM) where
  map := .map
