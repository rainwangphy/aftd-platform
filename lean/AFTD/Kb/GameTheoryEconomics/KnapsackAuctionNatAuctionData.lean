import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers

/-!
# KnapsackAuction.natAuctionData

Topic: mechanism_design   Node: f3166f6f7b04

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.natAuctionData`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The knapsack-auction data obtained from natural-number weights and capacity, with dummy zero allocation/payment rules. This is only used to instantiate the fractional greedy construction.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I] in
/-- The knapsack-auction data obtained from natural-number weights and capacity, with dummy zero allocation/payment rules. This is only used to instantiate the fractional greedy construction. -/
def KnapsackAuction.natAuctionData (w : I → Nat) (capacity : Nat) : KnapsackAuction I ℝ where
  allocationRule := fun _ _ => 0
  paymentRule := fun _ _ => 0
  weight := fun i => (w i : ℝ)
  totalCapacity := capacity
