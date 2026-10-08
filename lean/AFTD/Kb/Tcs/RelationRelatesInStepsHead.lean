import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesInSteps
import AFTD.Kb.Tcs.RelationRelatesInStepsSingle

/-!
# Relation.RelatesInSteps.head

Topic: algorithms   Node: 2ad9a6f3ddb3

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesInSteps.head`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.RelatesInSteps.head
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
theorem Relation.RelatesInSteps.head (t t' t'' : α) (n : ℕ) (h₁ : r t t')
    (h₂ : RelatesInSteps r t' t'' n) : RelatesInSteps r t t'' (n+1) := by
  induction h₂ with
  | refl =>
    exact single h₁
  | tail _ _ n _ hcd hac =>
    exact tail _ _ _ (n + 1) hac hcd
