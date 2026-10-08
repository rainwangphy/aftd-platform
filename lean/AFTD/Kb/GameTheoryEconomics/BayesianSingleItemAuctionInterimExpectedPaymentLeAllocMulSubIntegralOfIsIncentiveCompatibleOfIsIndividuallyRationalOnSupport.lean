import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsIncentiveCompatible
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsIndividuallyRationalOnSupport
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimExpectedPayment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasInterimPaymentFormula
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasInterimPaymentFormulaOfIsIncentiveCompatible
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimExpectedPaymentZeroNonposOfIsIndividuallyRationalOnSupport
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionUpdateReportProfileSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivApplyFst
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivApplySnd
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivSymmApply
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionExpectedSellerRevenueInEnvironmentSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.interimExpectedPayment_le_alloc_mul_sub_integral_of_isIncentiveCompatible_of_isIndividuallyRationalOnSupport

Topic: mechanism_design   Node: 7360779621fc

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.interimExpectedPayment_le_alloc_mul_sub_integral_of_isIncentiveCompatible_of_isIndividuallyRationalOnSupport`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IC and IR bound interim expected payment by the envelope term.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- IC and IR bound interim expected payment by the envelope term. -/
theorem BayesianSingleItemAuction.interimExpectedPayment_le_alloc_mul_sub_integral_of_isIncentiveCompatible_of_isIndividuallyRationalOnSupport
    (A : BayesianSingleItemAuction I)
    (hIC : A.IsIncentiveCompatible)
    (hIR : A.IsIndividuallyRationalOnSupport)
    (i : I) (v_i : ℝ) :
    A.interimExpectedPayment i v_i ≤
      A.interimAllocProb i v_i * v_i -
        ∫ z in 0..v_i, A.interimAllocProb i z := by
  have hpay := A.hasInterimPaymentFormula_of_isIncentiveCompatible hIC
  have hM0 := A.interimExpectedPayment_zero_nonpos_of_isIndividuallyRationalOnSupport hIR i
  calc
    A.interimExpectedPayment i v_i
        = A.interimExpectedPayment i 0 + A.interimAllocProb i v_i * v_i -
          ∫ z in 0..v_i, A.interimAllocProb i z := hpay i v_i
    _ ≤ A.interimAllocProb i v_i * v_i -
          ∫ z in 0..v_i, A.interimAllocProb i z := by
          linarith
