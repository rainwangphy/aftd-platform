import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesWithinSteps
import AFTD.Kb.Tcs.RelationRelatesInSteps
import AFTD.Kb.Tcs.RelationRelatesInStepsZero

/-!
# Relation.RelatesWithinSteps.zero

Topic: algorithms   Node: e1dd50a75e01

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesWithinSteps.zero`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.RelatesWithinSteps.zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
lemma Relation.RelatesWithinSteps.zero {a b : α} (h : RelatesWithinSteps r a b 0) : a = b := by
  obtain ⟨m, hm, hevals⟩ := h
  have : m = 0 := Nat.le_zero.mp hm
  subst this
  exact RelatesInSteps.zero hevals
