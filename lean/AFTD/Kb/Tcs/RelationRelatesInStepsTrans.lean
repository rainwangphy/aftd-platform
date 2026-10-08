import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesInSteps

/-!
# Relation.RelatesInSteps.trans

Topic: algorithms   Node: 32a8d2b99fc1

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesInSteps.trans`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.RelatesInSteps.trans
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
lemma Relation.RelatesInSteps.trans {a b c : α} {n m : ℕ}
    (h₁ : RelatesInSteps r a b n) (h₂ : RelatesInSteps r b c m) :
    RelatesInSteps r a c (n + m) := by
  induction h₂ generalizing a n with
  | refl => simp [h₁]
  | tail t' t'' k hsteps hstep ih =>
    rw [← Nat.add_assoc]
    exact .tail _ t' t'' (n + k) (ih h₁) hstep
