import AFTD.Prelude

/-!
# payoff_lt_of_price_lt

Topic: equilibria   Node: 59768c7a27f4

Provenance: formalization of a published result. Source: EconCSLib, `payoff_lt_of_price_lt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/OrderedGroup.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lowering the price by a positive amount strictly increases payoff.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
/-- Lowering the price by a positive amount strictly increases payoff. -/
theorem payoff_lt_of_price_lt {value price₁ price₂ : U} (h : price₁ < price₂) :
    value - price₂ < value - price₁ :=
  sub_lt_sub_iff_left value |>.mpr h
