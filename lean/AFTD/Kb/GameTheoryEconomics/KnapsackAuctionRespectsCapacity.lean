import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers

/-!
# KnapsackAuction.RespectsCapacity

Topic: mechanism_design   Node: da0898292295

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.RespectsCapacity`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The allocation rule respects the knapsack capacity constraint.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- The allocation rule respects the knapsack capacity constraint. -/
def KnapsackAuction.RespectsCapacity [Fintype I] (A : KnapsackAuction I U) : Prop :=
  ∀ b : I → U, (∑ i, A.weight i * A.allocationRule b i) ≤ A.totalCapacity
