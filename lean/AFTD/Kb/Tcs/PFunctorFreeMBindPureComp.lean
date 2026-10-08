import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMBind
import AFTD.Kb.Tcs.PFunctorFreeMInstPure
import AFTD.Kb.Tcs.PFunctorFreeMMap
import AFTD.Kb.Tcs.PFunctorFreeMBindEqBind
import AFTD.Kb.Tcs.PFunctorFreeMMapEqMap
import AFTD.Kb.Tcs.PFunctorFreeMBindPure
import AFTD.Kb.Tcs.CslibFreeMBind
import AFTD.Kb.Tcs.CslibFreeMBindPureComp

/-!
# PFunctor.FreeM.bind_pure_comp

Topic: algorithms   Node: c5560f36235f

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.bind_pure_comp`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.bind_pure_comp
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
@[simp]
lemma PFunctor.FreeM.bind_pure_comp (f : α → β) : ∀ x : P.FreeM α, x.bind (pure ∘ f) = map f x
  | .pure a => rfl
  | .liftBind a cont => by simp only [FreeM.bind, map, bind_pure_comp]
