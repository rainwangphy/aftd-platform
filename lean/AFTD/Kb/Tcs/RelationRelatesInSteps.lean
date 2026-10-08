import AFTD.Prelude

/-!
# Relation.RelatesInSteps

Topic: algorithms   Node: e1e20a9c1544

Provenance: formalization of a published result. Source: CSLib, `Relation.RelatesInSteps`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/RelatesInSteps.lean (Copyright (c) 2025 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A relation `r` relates two elements of `α` in `n` steps if there is a chain of `n` pairs `(t_i, t_{i+1})` such that `r t_i t_{i+1}` for each `i`, starting from the first element and ending at the second.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r : α → α → Prop} {a b c : α} in
/-- A relation `r` relates two elements of `α` in `n` steps if there is a chain of `n` pairs `(t_i, t_{i+1})` such that `r t_i t_{i+1}` for each `i`, starting from the first element and ending at the second. -/
inductive Relation.RelatesInSteps (r : α → α → Prop) : α → α → ℕ → Prop | refl (a : α) : RelatesInSteps r a a 0
  | tail (t t' t'' : α) (n : ℕ) (h₁ : RelatesInSteps r t t' n) (h₂ : r t' t'') :
      RelatesInSteps r t t'' (n + 1)
