import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFractionalSocialWelfare
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionRealBidOfNat
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatFractionalGreedyAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionCapacity

/-!
# KnapsackAuction.natFractionalGreedyValue

Topic: mechanism_design   Node: 4e650fd77c8a

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.natFractionalGreedyValue`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Welfare of the ratio-sorted fractional greedy allocation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I] in
/-- Welfare of the ratio-sorted fractional greedy allocation. -/
noncomputable def KnapsackAuction.natFractionalGreedyValue (w b : I → Nat) (capacity : Nat) : ℝ :=
  fractionalSocialWelfare (realBidOfNat b) (natFractionalGreedyAllocation w b capacity)
