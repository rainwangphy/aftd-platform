import AFTD.Prelude

/-!
# le_zero_of_add_le_self

Topic: equilibria   Node: 669ab8f59fe8

Provenance: formalization of a published result. Source: EconCSLib, `le_zero_of_add_le_self`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/OrderedGroup.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

In a zero-sum comparison: if `a + b ≤ a` then `b ≤ 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
/-- In a zero-sum comparison: if `a + b ≤ a` then `b ≤ 0`. -/
theorem le_zero_of_add_le_self {a b : U} (h : a + b ≤ a) : b ≤ 0 := by
  have := (add_le_add_iff_left a).mp (by rwa [add_zero] : a + b ≤ a + 0)
  exact this
