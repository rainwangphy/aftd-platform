import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFractionalSupportedOn

/-!
# KnapsackAuction.eq_zero_of_fractionalSupportedOn_of_not_mem

Topic: mechanism_design   Node: 12db9c4d0d0d

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.eq_zero_of_fractionalSupportedOn_of_not_mem`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.eq_zero_of_fractionalSupportedOn_of_not_mem
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I] in
omit [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I] in
lemma KnapsackAuction.eq_zero_of_fractionalSupportedOn_of_not_mem
    {items : List I} {x : I → ℝ}
    (hsupp : fractionalSupportedOn items x) {i : I} (hi : i ∉ items) :
    x i = 0 := by
  by_contra hxi
  exact hi (hsupp i hxi)
