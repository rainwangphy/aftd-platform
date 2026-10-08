import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesWithinSteps
import AFTD.Kb.Tcs.RelationRelatesInSteps
import AFTD.Kb.Tcs.RelationRelatesInStepsTrans
import AFTD.Kb.Tcs.RelationRelatesWithinStepsZeroIff

/-!
# Relation.RelatesWithinSteps.trans

Topic: algorithms   Node: dce0ee854216

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesWithinSteps.trans`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Transitivity of `RelatesWithinSteps` in the sum of the step bounds.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
/-- Transitivity of `RelatesWithinSteps` in the sum of the step bounds. -/
@[trans]
lemma Relation.RelatesWithinSteps.trans {a b c : α} {n₁ n₂ : ℕ}
    (h₁ : RelatesWithinSteps r a b n₁) (h₂ : RelatesWithinSteps r b c n₂) :
    RelatesWithinSteps r a c (n₁ + n₂) := by
  obtain ⟨m₁, hm₁, hevals₁⟩ := h₁
  obtain ⟨m₂, hm₂, hevals₂⟩ := h₂
  use m₁ + m₂
  constructor
  · lia
  · exact RelatesInSteps.trans hevals₁ hevals₂
