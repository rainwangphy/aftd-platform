import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesInSteps
import AFTD.Kb.Tcs.RelationRelatesInStepsSucc

/-!
# Relation.RelatesInSteps.succ_iff

Topic: algorithms   Node: 210c4d071368

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesInSteps.succ_iff`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.RelatesInSteps.succ_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
lemma Relation.RelatesInSteps.succ_iff {a b : α} {n : ℕ} :
    RelatesInSteps r a b (n + 1) ↔ ∃ t', RelatesInSteps r a t' n ∧ r t' b := by
  constructor
  · exact RelatesInSteps.succ
  · rintro ⟨t', h_steps, h_red⟩
    exact .tail _ t' b n h_steps h_red
