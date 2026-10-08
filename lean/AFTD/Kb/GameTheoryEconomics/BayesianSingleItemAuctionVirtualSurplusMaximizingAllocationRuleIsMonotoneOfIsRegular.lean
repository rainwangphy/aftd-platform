import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsRegular
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsMonotone
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAllocationRule
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingPaymentRule
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingWinner
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingWinnerUpdateSelfOfWinner
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualValue
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionWinningVirtualValue
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionWinningVirtualValueUpdateSelfPosIffOfWinner
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAllocationRuleEqOneOfWinnerOfWinningPos
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAllocationRuleEqZeroOfNotPos
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAllocationRuleNonneg
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAllocationRuleEqZeroOfNeWinner
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
# BayesianSingleItemAuction.virtualSurplusMaximizingAllocationRule_isMonotone_of_isRegular

Topic: mechanism_design   Node: 8116051c0707

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.virtualSurplusMaximizingAllocationRule_isMonotone_of_isRegular`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Under regularity, the deterministic virtual-surplus-maximizing allocation rule is monotone in the sense required by `SingleParameterMechanism`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
/-- Under regularity, the deterministic virtual-surplus-maximizing allocation rule is monotone in the sense required by `SingleParameterMechanism`. -/
theorem BayesianSingleItemAuction.virtualSurplusMaximizingAllocationRule_isMonotone_of_isRegular
    [Fintype I] [Nontrivial I] [DecidableEq I] [LinearOrder I]
    (A : BayesianSingleItemAuction I) (hA : A.IsRegular) :
    SingleParameterMechanism.IsMonotone
      ({ allocationRule := A.virtualSurplusMaximizingAllocationRule
         paymentRule := A.virtualSurplusMaximizingPaymentRule } :
        SingleParameterMechanism I ℝ) := by
  classical
  intro i r s hrs b
  change
    A.virtualSurplusMaximizingAllocationRule (Function.update b i r) i ≤
      A.virtualSurplusMaximizingAllocationRule (Function.update b i s) i
  by_cases hwin_lo :
      A.virtualSurplusMaximizingWinner (Function.update b i r) = i
  · have hwin_hi :
        A.virtualSurplusMaximizingWinner (Function.update b i s) = i :=
      A.virtualSurplusMaximizingWinner_update_self_of_winner hA b i hrs hwin_lo
    by_cases hpos_lo : 0 < A.virtualValue i r
    · have hpos_hi : 0 < A.virtualValue i s := lt_of_lt_of_le hpos_lo (hA i hrs)
      have hpos_lo' :
          0 < A.winningVirtualValue (Function.update b i r) :=
        (A.winningVirtualValue_update_self_pos_iff_of_winner b i r hwin_lo).2 hpos_lo
      have hpos_hi' :
          0 < A.winningVirtualValue (Function.update b i s) :=
        (A.winningVirtualValue_update_self_pos_iff_of_winner b i s hwin_hi).2 hpos_hi
      rw [A.virtualSurplusMaximizingAllocationRule_eq_one_of_winner_of_winning_pos hwin_lo
          hpos_lo',
        A.virtualSurplusMaximizingAllocationRule_eq_one_of_winner_of_winning_pos hwin_hi
          hpos_hi']
    · have hnotpos_lo :
          ¬ 0 < A.winningVirtualValue (Function.update b i r) :=
        mt (A.winningVirtualValue_update_self_pos_iff_of_winner b i r hwin_lo).1 hpos_lo
      rw [A.virtualSurplusMaximizingAllocationRule_eq_zero_of_not_pos
        (Function.update b i r) hnotpos_lo]
      exact A.virtualSurplusMaximizingAllocationRule_nonneg (Function.update b i s) i
  · have hi_ne : i ≠ A.virtualSurplusMaximizingWinner (Function.update b i r) :=
      fun hi => hwin_lo hi.symm
    rw [A.virtualSurplusMaximizingAllocationRule_eq_zero_of_ne_winner hi_ne]
    exact A.virtualSurplusMaximizingAllocationRule_nonneg (Function.update b i s) i
