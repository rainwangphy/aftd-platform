import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatFractionalGreedyValue
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionIntegralGreedyValue
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionHighestBidValue
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionSortedAgentsByRatio
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatAuctionData
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionRealBidOfNat
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionRatioTieKey
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionFractionalSocialWelfare
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatFractionalGreedyList
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatBinarySocialWelfare
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionIntegralGreedyList
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatFractionalGreedyListLeIntegralGreedyListPlusHighest
import AFTD.Kb.GameTheoryEconomics.KnapsackAuction
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionCapacity
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionIntegralGreedyAllocation
import AFTD.Kb.GameTheoryEconomics.KnapsackAuctionNatFractionalGreedyAllocation

/-!
# KnapsackAuction.natFractionalGreedyValue_le_integralGreedyValue_plus_highest

Topic: mechanism_design   Node: f89cc249dad8

Provenance: formalization of a published result. Source: EconCSLib, `KnapsackAuction.natFractionalGreedyValue_le_integralGreedyValue_plus_highest`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Knapsack.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

KnapsackAuction.natFractionalGreedyValue_le_integralGreedyValue_plus_highest
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KnapsackAuction in
open scoped BigOperators in
variable {I : Type*} [Fintype I] [DecidableEq I] [LinearOrder I] [Nonempty I] in
lemma KnapsackAuction.natFractionalGreedyValue_le_integralGreedyValue_plus_highest
    (w b : I → Nat) (capacity : Nat) (hwpos : ∀ i, 0 < w i) :
    natFractionalGreedyValue w b capacity ≤
      integralGreedyValue w b capacity + highestBidValue b := by
  classical
  have hnodup :
      ((natAuctionData w capacity).sortedAgentsByRatio (realBidOfNat b)).Nodup := by
    simpa [sortedAgentsByRatio] using
      ((List.nodup_mergeSort
          (l := (Finset.univ : Finset I).toList)
          (le := fun i j =>
            decide
              ((natAuctionData w capacity).ratioTieKey (realBidOfNat b) i ≤
                (natAuctionData w capacity).ratioTieKey (realBidOfNat b) j))).2
        (by simpa using (Finset.nodup_toList (s := (Finset.univ : Finset I)))))
  simpa [natFractionalGreedyValue, natFractionalGreedyAllocation,
    integralGreedyValue, integralGreedyAllocation] using
    (natFractionalGreedyList_le_integralGreedyList_plus_highest
      (w := w) (b := b) hwpos hnodup capacity)
