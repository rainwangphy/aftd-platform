import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsZeroNormalized
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasInterimPaymentFormula
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEnvelopeVirtualSurplusAnalyticAssumptions
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimExpectedPayment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeDensity
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualValue
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasInterimPaymentEnvelopeIdentityOfZeroNormalizedOfInterimPaymentFormula
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEnvelopeVirtualSurplusAnalyticAssumptionsEnvelopeIntegralEqVirtualSurplusIntegral
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
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingMechanismEqWithMyersonPayment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingPaymentRuleEq
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualSurplusMaximizingAuctionHasSameSellingEnvironment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.hasInterimPaymentVirtualSurplusIdentity_of_zeroNormalized_of_interimPaymentFormula

Topic: mechanism_design   Node: 6af13918abc4

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.hasInterimPaymentVirtualSurplusIdentity_of_zeroNormalized_of_interimPaymentFormula`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BayesianSingleItemAuction.hasInterimPaymentVirtualSurplusIdentity_of_zeroNormalized_of_interimPaymentFormula
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
theorem BayesianSingleItemAuction.hasInterimPaymentVirtualSurplusIdentity_of_zeroNormalized_of_interimPaymentFormula
    [Fintype I] [DecidableEq I] (A B : BayesianSingleItemAuction I)
    (hzero : B.IsZeroNormalized)
    (hpay_formula : B.HasInterimPaymentFormula)
    (henv :
      A.EnvelopeVirtualSurplusAnalyticAssumptions B) :
    ∀ i : I,
      (∫ v in 0..A.typeData.omega i, B.interimExpectedPayment i v * A.typeDensity i v) =
        ∫ v in 0..A.typeData.omega i,
          B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v := by
  intro i
  calc
    (∫ v in 0..A.typeData.omega i, B.interimExpectedPayment i v * A.typeDensity i v)
        = ∫ v in 0..A.typeData.omega i,
            (B.interimAllocProb i v * v -
              ∫ z in 0..v, B.interimAllocProb i z) * A.typeDensity i v :=
          A.hasInterimPaymentEnvelopeIdentity_of_zeroNormalized_of_interimPaymentFormula
            B hzero hpay_formula i
    _ = ∫ v in 0..A.typeData.omega i,
          B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v :=
          henv.envelopeIntegral_eq_virtualSurplusIntegral i
