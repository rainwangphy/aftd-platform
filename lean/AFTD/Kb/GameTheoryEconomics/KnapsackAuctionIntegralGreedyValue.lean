import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatBinarySocialWelfare
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionIntegralGreedyAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionCapacity

/-!
# KnapsackAuction.integralGreedyValue

Topic: mechanism_design   Node: b6d0eb996a15

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.integralGreedyValue`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Welfare of the ratio-sorted integral greedy allocation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I] in
/-- Welfare of the ratio-sorted integral greedy allocation. -/
noncomputable def KnapsackAuction.integralGreedyValue (w b : I → Nat) (capacity : Nat) : Nat :=
  natBinarySocialWelfare b (integralGreedyAllocation w b capacity)
