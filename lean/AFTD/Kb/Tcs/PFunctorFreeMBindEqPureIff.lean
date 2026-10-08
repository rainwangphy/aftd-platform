import AFTD.Prelude
import AFTD.Kb.Tcs.PFunctorFreeM
import AFTD.Kb.Tcs.PFunctorFreeMBind
import AFTD.Kb.Tcs.PFunctorFreeMInstPure
import AFTD.Kb.Tcs.PFunctorFreeMBindEqBind
import AFTD.Kb.Tcs.PFunctorFreeMBindPure
import AFTD.Kb.Tcs.PFunctorFreeMBindPureComp
import AFTD.Kb.Tcs.CslibFreeMBind

/-!
# PFunctor.FreeM.bind_eq_pure_iff

Topic: algorithms   Node: 04376d1c10c4

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM.bind_eq_pure_iff`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

PFunctor.FreeM.bind_eq_pure_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
variable {P : PFunctor.{uA, uB}} {α β γ : Type*} in
@[simp] lemma PFunctor.FreeM.bind_eq_pure_iff (x : P.FreeM α) (f : α → P.FreeM β) (b : β) :
    x.bind f = pure b ↔ ∃ a, x = pure a ∧ f a = pure b := by
  cases x with
  | pure a => exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, h, hf⟩ => by cases h; exact hf⟩
  | liftBind a cont =>
    constructor
    · intro h
      cases h
    · rintro ⟨_, h, _⟩
      cases h
