import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesWithinSteps
import AFTD.Kb.Tcs.RelationRelatesWithinStepsOfRelatesInSteps
import AFTD.Kb.Tcs.RelationRelatesInStepsSingle

/-!
# Relation.RelatesWithinSteps.single

Topic: algorithms   Node: 7f4d0d138e5f

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesWithinSteps.single`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.RelatesWithinSteps.single
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
lemma Relation.RelatesWithinSteps.single {a b : α} (h : r a b) : RelatesWithinSteps r a b 1 :=
  RelatesWithinSteps.of_relatesInSteps (RelatesInSteps.single h)
