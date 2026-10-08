import AFTD.Prelude

/-!
# payoff_nonpos_iff

Topic: equilibria   Node: e18454d4dcc3

Provenance: formalization of a published result. Source: EconCSLib, `payoff_nonpos_iff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/OrderedGroup.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Winning is unprofitable iff the price exceeds the value.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
/-- Winning is unprofitable iff the price exceeds the value. -/
theorem payoff_nonpos_iff {value price : U} :
    value - price ≤ 0 ↔ value ≤ price :=
  sub_nonpos
