import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFreeMCompMap
import AFTD.Kb.Tcs.PFunctorFreeMIdMap
import AFTD.Kb.Tcs.PFunctorFreeMMapEqMap
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMBindPureComp
import AFTD.Kb.Tcs.PFunctorFreeMMap

/-!
# PFunctor.FreeM.comp_map

Topic: algorithms   Node: efbac4e49ba6

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.comp_map`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.comp_map
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
theorem PFunctor.FreeM.comp_map (h : β → γ) (g : α → β) :
    ∀ x : P.FreeM α, map (h ∘ g) x = map h (map g x)
  | .pure a => rfl
  | .liftBind a cont => by
    simp only [map]
    congr 1
    funext u
    exact comp_map h g (cont u)
