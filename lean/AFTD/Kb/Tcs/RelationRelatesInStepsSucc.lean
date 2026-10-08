import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesInSteps

/-!
# Relation.RelatesInSteps.succ

Topic: algorithms   Node: ec960149f330

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesInSteps.succ`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.RelatesInSteps.succ
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
lemma Relation.RelatesInSteps.succ {n : ℕ} (h : RelatesInSteps r a b (n + 1)) :
    ∃ t', RelatesInSteps r a t' n ∧ r t' b := by
  cases h with
  | tail t' _ _ hsteps hstep => exact ⟨t', hsteps, hstep⟩
