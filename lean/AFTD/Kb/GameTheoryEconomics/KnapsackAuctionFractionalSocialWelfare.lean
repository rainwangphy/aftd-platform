import AFTD.Prelude

/-!
# KnapsackAuction.fractionalSocialWelfare

Topic: mechanism_design   Node: 38b7409f7b9c

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.fractionalSocialWelfare`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fractional social welfare for a `U`-valued allocation vector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable [Fintype I] [DecidableEq I] [LinearOrder I] in
/-- Fractional social welfare for a `U`-valued allocation vector. -/
def KnapsackAuction.fractionalSocialWelfare (b : I → U) (x : I → U) : U :=
  ∑ i, b i * x i
