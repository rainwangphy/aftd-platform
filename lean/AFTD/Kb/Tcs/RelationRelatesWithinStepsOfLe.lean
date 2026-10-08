import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesWithinSteps
import AFTD.Kb.Tcs.RelationRelatesInSteps
import AFTD.Kb.Tcs.RelationRelatesWithinStepsZeroIff

/-!
# Relation.RelatesWithinSteps.of_le

Topic: algorithms   Node: 341d7041d01c

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesWithinSteps.of_le`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.RelatesWithinSteps.of_le
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
lemma Relation.RelatesWithinSteps.of_le {a b : α} {n₁ n₂ : ℕ}
    (h : RelatesWithinSteps r a b n₁) (hn : n₁ ≤ n₂) :
    RelatesWithinSteps r a b n₂ := by
  obtain ⟨m, hm, hevals⟩ := h
  exact ⟨m, Nat.le_trans hm hn, hevals⟩
