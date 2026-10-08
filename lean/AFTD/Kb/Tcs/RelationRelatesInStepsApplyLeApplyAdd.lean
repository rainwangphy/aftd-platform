import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesInSteps

/-!
# Relation.RelatesInSteps.apply_le_apply_add

Topic: algorithms   Node: e414fce5d102

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesInSteps.apply_le_apply_add`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If `h : α → ℕ` increases by at most 1 on each step of `r`, then the value of `h` at the output is at most `h` at the input plus the number of steps.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
/-- If `h : α → ℕ` increases by at most 1 on each step of `r`, then the value of `h` at the output is at most `h` at the input plus the number of steps. -/
lemma Relation.RelatesInSteps.apply_le_apply_add {a b : α} {m : ℕ} (hevals : RelatesInSteps r a b m)
    (h : α → ℕ) (h_step : ∀ a b, r a b → h b ≤ h a + 1) :
    h b ≤ h a + m := by
  induction hevals with
  | refl => simp
  | tail t' t'' k _ hstep ih =>
    have h_step' := h_step t' t'' hstep
    lia
