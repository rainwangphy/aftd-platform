import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesInSteps

/-!
# Relation.RelatesInSteps.reflTransGen

Topic: algorithms   Node: b386420c4838

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesInSteps.reflTransGen`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.RelatesInSteps.reflTransGen
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
theorem Relation.RelatesInSteps.reflTransGen (h : RelatesInSteps r a b n) : ReflTransGen r a b := by
  induction h with
  | refl => rfl
  | tail _ _ _ _ h ih => exact .tail ih h
