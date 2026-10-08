import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesInSteps

/-!
# Relation.RelatesWithinSteps

Topic: algorithms   Node: 5b6302f5b8c1

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesWithinSteps`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`RelatesWithinSteps` is a variant of `RelatesInSteps` that allows for a loose bound. It states that `a` relates to `b` in *at most* `n` steps.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
/-- `RelatesWithinSteps` is a variant of `RelatesInSteps` that allows for a loose bound. It states that `a` relates to `b` in *at most* `n` steps. -/
def Relation.RelatesWithinSteps (r : α → α → Prop) (a b : α) (n : ℕ) : Prop :=
  ∃ m ≤ n, RelatesInSteps r a b m
