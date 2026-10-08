import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesInSteps
import AFTD.Kb.Tcs.RelationRelatesInStepsSucc'
import AFTD.Kb.Tcs.RelationRelatesInStepsHead

/-!
# Relation.RelatesInSteps.succ'_iff

Topic: algorithms   Node: f8a4dfc075d7

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesInSteps.succ'_iff`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.RelatesInSteps.succ'_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
lemma Relation.RelatesInSteps.succ'_iff {a b : α} {n : ℕ} :
    RelatesInSteps r a b (n + 1) ↔ ∃ t', r a t' ∧ RelatesInSteps r t' b n := by
  constructor
  · exact succ'
  · rintro ⟨t', h_red, h_steps⟩
    exact h_steps.head a t' b n h_red
