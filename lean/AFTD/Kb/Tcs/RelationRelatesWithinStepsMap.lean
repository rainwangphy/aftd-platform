import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesInStepsMap
import AFTD.Kb.Tcs.RelationRelatesWithinSteps
import AFTD.Kb.Tcs.RelationRelatesWithinStepsZeroIff
import AFTD.Kb.Tcs.RelationRelatesInSteps

/-!
# Relation.RelatesWithinSteps.map

Topic: algorithms   Node: 200f0d0849bc

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesWithinSteps.map`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If `g` is a homomorphism from `r` to `r'` (i.e., it preserves the reduction relation), then `RelatesWithinSteps` is preserved under `g`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
/-- If `g` is a homomorphism from `r` to `r'` (i.e., it preserves the reduction relation), then `RelatesWithinSteps` is preserved under `g`. -/
lemma Relation.RelatesWithinSteps.map {α α' : Type*} {r : α → α → Prop} {r' : α' → α' → Prop}
    (g : α → α') (hg : ∀ a b, r a b → r' (g a) (g b))
    {a b : α} {n : ℕ} (h : RelatesWithinSteps r a b n) :
    RelatesWithinSteps r' (g a) (g b) n := by
  obtain ⟨m, hm, hevals⟩ := h
  exact ⟨m, hm, RelatesInSteps.map g hg hevals⟩
