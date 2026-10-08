import AFTD.Prelude
import AFTD.Kb.Tcs.RelationRelatesInSteps
import AFTD.Kb.Tcs.G

/-!
# Relation.RelatesInSteps.map

Topic: algorithms   Node: 03d0da58a7d0

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesInSteps.map`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If `g` is a homomorphism from `r` to `r'` (i.e., it preserves the reduction relation), then `RelatesInSteps` is preserved under `g`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
/-- If `g` is a homomorphism from `r` to `r'` (i.e., it preserves the reduction relation), then `RelatesInSteps` is preserved under `g`. -/
lemma Relation.RelatesInSteps.map {α α' : Type*}
    {r : α → α → Prop} {r' : α' → α' → Prop}
    (g : α → α') (hg : ∀ a b, r a b → r' (g a) (g b))
    {a b : α} {n : ℕ} (h : RelatesInSteps r a b n) :
    RelatesInSteps r' (g a) (g b) n := by
  induction h with
  | refl => exact RelatesInSteps.refl (g _)
  | tail t' t'' m _ hstep ih =>
    exact .tail (g _) (g t') (g t'') m ih (hg t' t'' hstep)
