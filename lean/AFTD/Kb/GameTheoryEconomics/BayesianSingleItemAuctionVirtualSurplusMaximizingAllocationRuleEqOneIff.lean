import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAllocationRule
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionWinningVirtualValue
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingWinner
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAllocationRuleEqZeroOfNeWinner
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAllocationRuleEqZeroOfNotPos
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAllocationRuleEqOneOfWinnerOfWinningPos
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionUpdateReportProfileSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivApplyFst
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivApplySnd
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivSymmApply
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionExpectedSellerRevenueInEnvironmentSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingMechanismAllocationRule
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingMechanismPaymentRule
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionAllocationRule
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionPaymentRule
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionTypeData
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionToSingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionToDirectBayesianMechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.virtualSurplusMaximizingAllocationRule_eq_one_iff

Topic: mechanism_design   Node: 4132281f02cc

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.virtualSurplusMaximizingAllocationRule_eq_one_iff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Allocation probability `1` characterizes the positive virtual-value winner.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
/-- Allocation probability `1` characterizes the positive virtual-value winner. -/
theorem BayesianSingleItemAuction.virtualSurplusMaximizingAllocationRule_eq_one_iff
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (b : I → ℝ) (i : I) :
    A.virtualSurplusMaximizingAllocationRule b i = 1 ↔
      0 < A.winningVirtualValue b ∧ i = A.virtualSurplusMaximizingWinner b := by
  constructor
  · intro hi
    by_cases hpos : 0 < A.winningVirtualValue b
    · refine ⟨hpos, ?_⟩
      by_contra hne
      have hzero : A.virtualSurplusMaximizingAllocationRule b i = 0 :=
        A.virtualSurplusMaximizingAllocationRule_eq_zero_of_ne_winner hne
      exact zero_ne_one (hzero.symm.trans hi)
    · have hzero : A.virtualSurplusMaximizingAllocationRule b i = 0 := by
        simpa using
          congr_fun (A.virtualSurplusMaximizingAllocationRule_eq_zero_of_not_pos b hpos) i
      exact False.elim (zero_ne_one (by rw [← hzero, hi]))
  · rintro ⟨hpos, hi⟩
    exact A.virtualSurplusMaximizingAllocationRule_eq_one_of_winner_of_winning_pos
      hi.symm hpos
