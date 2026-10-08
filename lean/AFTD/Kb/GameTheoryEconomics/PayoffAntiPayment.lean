import AFTD.Prelude

/-!
# payoff_anti_payment

Topic: equilibria   Node: 6caf75cc0007

Provenance: formalization of a published result. Source: EconCSLib, `payoff_anti_payment`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/OrderedGroup.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If paying less is better: `price₁ ≤ price₂ → value - price₂ ≤ value - price₁`. Useful for comparing utilities when the allocation is the same but payments differ.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {U : Type*} [AddCommGroup U] [LinearOrder U] [IsOrderedAddMonoid U] in
/-- If paying less is better: `price₁ ≤ price₂ → value - price₂ ≤ value - price₁`. Useful for comparing utilities when the allocation is the same but payments differ. -/
theorem payoff_anti_payment {value price₁ price₂ : U} (h : price₁ ≤ price₂) :
    value - price₂ ≤ value - price₁ :=
  sub_le_sub_iff_left value |>.mpr h
