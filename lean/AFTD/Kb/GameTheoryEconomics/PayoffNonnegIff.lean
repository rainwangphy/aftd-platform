import AFTD.Prelude

/-!
# payoff_nonneg_iff

Topic: equilibria   Node: 67e7ef0e14f4

Provenance: formalization of a published result. Source: EconCSLib, `payoff_nonneg_iff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/OrderedGroup.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Winning is profitable iff the value exceeds the price.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
/-- Winning is profitable iff the value exceeds the price. -/
theorem payoff_nonneg_iff {value price : U} :
    0 ≤ value - price ↔ price ≤ value :=
  sub_nonneg
