import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsAllocFeasible
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionRespectsCapacity

/-!
# KnapsackAuction.IsFeasible

Topic: mechanism_design   Node: 895235b42091

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.IsFeasible`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Feasibility for a knapsack auction: * each agent's allocation lies in `[0,1]` * the weighted allocation satisfies the total capacity bound
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- Feasibility for a knapsack auction: * each agent's allocation lies in `[0,1]` * the weighted allocation satisfies the total capacity bound -/
def KnapsackAuction.IsFeasible [Fintype I] (A : KnapsackAuction I U) : Prop :=
  A.IsAllocFeasible ∧ A.RespectsCapacity
