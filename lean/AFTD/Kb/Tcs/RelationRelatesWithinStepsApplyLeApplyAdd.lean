import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesWithinSteps
import AFTD.Kb.Tcs.RelationRelatesInSteps
import AFTD.Kb.Tcs.RelationRelatesInStepsApplyLeApplyAdd
import AFTD.Kb.Tcs.RelationRelatesWithinStepsZeroIff

/-!
# Relation.RelatesWithinSteps.apply_le_apply_add

Topic: algorithms   Node: 9ade47b92a32

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesWithinSteps.apply_le_apply_add`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If `h : α → ℕ` increases by at most 1 on each step of `r`, then the value of `h` at the output is at most `h` at the input plus the step bound.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
/-- If `h : α → ℕ` increases by at most 1 on each step of `r`, then the value of `h` at the output is at most `h` at the input plus the step bound. -/
lemma Relation.RelatesWithinSteps.apply_le_apply_add {a b : α} {m : ℕ} (hevals : RelatesWithinSteps r a b m)
    (h : α → ℕ) (h_step : ∀ a b, r a b → h b ≤ h a + 1)
    :
    h b ≤ h a + m := by
  obtain ⟨m, hm, hevals_m⟩ := hevals
  have := RelatesInSteps.apply_le_apply_add hevals_m h h_step
  lia
