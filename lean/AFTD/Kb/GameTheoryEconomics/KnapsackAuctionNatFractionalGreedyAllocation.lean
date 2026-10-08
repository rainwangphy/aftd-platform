import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatFractionalGreedyList
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionSortedAgentsByRatio
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatAuctionData
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionRealBidOfNat
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionCapacity

/-!
# KnapsackAuction.natFractionalGreedyAllocation

Topic: mechanism_design   Node: c96d6755e070

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.natFractionalGreedyAllocation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The ratio-sorted fractional greedy allocation on natural-number data.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I] in
/-- The ratio-sorted fractional greedy allocation on natural-number data. -/
noncomputable def KnapsackAuction.natFractionalGreedyAllocation (w b : I → Nat) (capacity : Nat) : I → ℝ :=
  natFractionalGreedyList w ((natAuctionData w capacity).sortedAgentsByRatio (realBidOfNat b)) capacity
