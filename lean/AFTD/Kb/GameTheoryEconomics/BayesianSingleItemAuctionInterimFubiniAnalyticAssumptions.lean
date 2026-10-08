import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionVirtualValue
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimExpectedPayment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeDensity
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
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
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.InterimFubiniAnalyticAssumptions

Topic: mechanism_design   Node: 70dc798dd1be

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.InterimFubiniAnalyticAssumptions`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fubini hypotheses connecting ex-ante and interim expressions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
/-- Fubini hypotheses connecting ex-ante and interim expressions. -/
structure BayesianSingleItemAuction.InterimFubiniAnalyticAssumptions [Fintype I]
    (A B : BayesianSingleItemAuction I) : Prop where
  payment_integrable :
    ∀ i : I, Integrable (fun t => B.paymentRule t i) A.prior
  virtual_surplus_integrable :
    ∀ i : I, Integrable (fun t => B.allocationRule t i * A.virtualValue i (t i)) A.prior
  payment_interim_fubini :
    ∀ i : I,
      (∫ t, B.paymentRule t i ∂A.prior) =
        ∫ v in 0..A.typeData.omega i, B.interimExpectedPayment i v * A.typeDensity i v
  virtual_surplus_interim_fubini :
    ∀ i : I,
      (∫ t, B.allocationRule t i * A.virtualValue i (t i) ∂A.prior) =
        ∫ v in 0..A.typeData.omega i,
          B.interimAllocProb i v * A.virtualValue i v * A.typeDensity i v
