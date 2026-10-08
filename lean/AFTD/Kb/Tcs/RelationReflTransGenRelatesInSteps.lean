import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesInSteps

/-!
# Relation.ReflTransGen.relatesInSteps

Topic: algorithms   Node: 528e1ae81f69

Provenance: formalization of a published result. Source: CSLib, `Relation.ReflTransGen.relatesInSteps`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.ReflTransGen.relatesInSteps
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
theorem Relation.ReflTransGen.relatesInSteps (h : ReflTransGen r a b) : ∃ n, RelatesInSteps r a b n := by
  induction h with
  | refl => exact ⟨0, .refl a⟩
  | tail _ _ ih =>
    obtain ⟨n, _⟩ := ih
    exact ⟨n + 1, by grind [RelatesInSteps]⟩
