import AFTD.Prelude

/-!
# nonneg_of_self_le_add

Topic: equilibria   Node: e15a26e9e12f

Provenance: formalization of a published result. Source: EconCSLib, `nonneg_of_self_le_add`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/OrderedGroup.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

In a zero-sum comparison: if `a ≤ a + b` then `0 ≤ b`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
/-- In a zero-sum comparison: if `a ≤ a + b` then `0 ≤ b`. -/
theorem nonneg_of_self_le_add {a b : U} (h : a ≤ a + b) : 0 ≤ b := by
  have := (add_le_add_iff_left a).mp (by rwa [add_zero] : a + 0 ≤ a + b)
  exact this
