import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionRatioTieKey
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# KnapsackAuction.sortedAgentsByRatio

Topic: mechanism_design   Node: dc9691756539

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.sortedAgentsByRatio`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Agents sorted by decreasing value-to-weight ratio, with lexicographic tie-breaking via the ambient order on `I`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable [Fintype I] [DecidableEq I] [LinearOrder I] in
/-- Agents sorted by decreasing value-to-weight ratio, with lexicographic tie-breaking via the ambient order on `I`. -/
noncomputable def KnapsackAuction.sortedAgentsByRatio (A : KnapsackAuction I U) (b : I → U) : List I :=
  by
    classical
    exact ((Finset.univ : Finset I).toList).mergeSort
      (fun i j => decide (A.ratioTieKey b i ≤ A.ratioTieKey b j))
