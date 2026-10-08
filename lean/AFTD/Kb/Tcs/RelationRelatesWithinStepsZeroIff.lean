import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesWithinSteps
import AFTD.Kb.Tcs.RelationRelatesWithinStepsZero
import AFTD.Kb.Tcs.RelationRelatesWithinStepsRefl

/-!
# Relation.RelatesWithinSteps.zero_iff

Topic: algorithms   Node: c85b553da3dd

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesWithinSteps.zero_iff`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.RelatesWithinSteps.zero_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
@[simp]
lemma Relation.RelatesWithinSteps.zero_iff {a b : α} : RelatesWithinSteps r a b 0 ↔ a = b := by
  constructor
  · exact RelatesWithinSteps.zero
  · intro h
    subst h
    exact RelatesWithinSteps.refl a
