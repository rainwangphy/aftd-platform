import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMMap
import AFTD.Kb.Tcs.PFunctorFreeMInstFunctor
import AFTD.Kb.Tcs.CslibFreeMMap
import AFTD.Kb.Tcs.CslibFreeMMapEqMap

/-!
# PFunctor.FreeM.map_eq_map

Topic: algorithms   Node: 50820721b7b5

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.map_eq_map`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Note that this lemma does not always apply, as it is universe-constrained by `Functor.map`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
/-- Note that this lemma does not always apply, as it is universe-constrained by `Functor.map`. -/
@[simp]
theorem PFunctor.FreeM.map_eq_map {α β : Type v} :
    FreeM.map (P := P) (α := α) (β := β) = Functor.map := rfl
