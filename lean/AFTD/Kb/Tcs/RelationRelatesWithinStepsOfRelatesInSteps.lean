import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesInSteps
import AFTD.Kb.Tcs.RelationRelatesWithinSteps

/-!
# Relation.RelatesWithinSteps.of_relatesInSteps

Topic: algorithms   Node: 72784deb9117

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesWithinSteps.of_relatesInSteps`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`RelatesInSteps` implies `RelatesWithinSteps` with the same bound.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
/-- `RelatesInSteps` implies `RelatesWithinSteps` with the same bound. -/
lemma Relation.RelatesWithinSteps.of_relatesInSteps {a b : α} {n : ℕ} (h : RelatesInSteps r a b n) :
    RelatesWithinSteps r a b n :=
  ⟨n, Nat.le_refl n, h⟩
