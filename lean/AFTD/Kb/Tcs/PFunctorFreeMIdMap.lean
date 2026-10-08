import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMMap
import AFTD.Kb.Tcs.PFunctorFreeMMapEqMap
import AFTD.Kb.Tcs.PFunctorFreeMBindPureComp
import AFTD.Kb.Tcs.CslibFreeMIdMap

/-!
# PFunctor.FreeM.id_map

Topic: algorithms   Node: 4894aa877103

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.id_map`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.id_map
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
@[simp]
theorem PFunctor.FreeM.id_map : ∀ x : P.FreeM α, map id x = x
  | .pure a => rfl
  | .liftBind a cont => by
    simp only [map]
    congr 1
    funext u
    exact id_map (cont u)
