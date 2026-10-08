import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionBinarySocialWelfare
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionWelfareMaximizer

/-!
# KnapsackAuction.maximalSocialWelfare

Topic: mechanism_design   Node: eb12aa97fff9

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.maximalSocialWelfare`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The maximal social welfare over the feasible binary allocation space.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} {U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable [Fintype I] [DecidableEq I] in
/-- The maximal social welfare over the feasible binary allocation space. -/
noncomputable def KnapsackAuction.maximalSocialWelfare
    (A : KnapsackAuction I U) (b : I → U) (hW : 0 ≤ A.totalCapacity) : U :=
  binarySocialWelfare b (A.welfareMaximizer b hW)
