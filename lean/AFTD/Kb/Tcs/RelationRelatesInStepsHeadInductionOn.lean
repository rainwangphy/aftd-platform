import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesInSteps
import AFTD.Kb.Tcs.RelationRelatesInStepsHead

/-!
# Relation.RelatesInSteps.head_induction_on

Topic: algorithms   Node: 36806acc854e

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesInSteps.head_induction_on`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.RelatesInSteps.head_induction_on
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
@[elab_as_elim]
theorem Relation.RelatesInSteps.head_induction_on {motive : ∀ (a : α) (n : ℕ), RelatesInSteps r a b n → Prop}
    {a : α} {n : ℕ} (h : RelatesInSteps r a b n) (hrefl : motive b 0 (.refl b))
    (hhead : ∀ {a c n} (h' : r a c) (h : RelatesInSteps r c b n),
      motive c n h → motive a (n + 1) (h.head a c b n h')) :
    motive a n h := by
  induction h with
  | refl => exact hrefl
  | tail t' b' m hstep hrt'b' hstep_ih =>
    apply hstep_ih
    · exact hhead hrt'b' _ hrefl
    · exact fun h1 h2 ↦ hhead h1 (.tail _ t' b' _ h2 hrt'b')
