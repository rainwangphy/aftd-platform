import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionPaymentInterimFubiniAssumptions
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasExpectedRevenueInterimPaymentIdentity
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimExpectedPayment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeDensity
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionExpectedInterimPaymentRevenue
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionExpectedPaymentRevenueInEnvironment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionExpectedSellerRevenueInEnvironment
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
# BayesianSingleItemAuction.PaymentInterimFubiniAssumptions.hasExpectedRevenueInterimPaymentIdentity

Topic: mechanism_design   Node: d3c75e941281

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.PaymentInterimFubiniAssumptions.hasExpectedRevenueInterimPaymentIdentity`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BayesianSingleItemAuction.PaymentInterimFubiniAssumptions.hasExpectedRevenueInterimPaymentIdentity
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
theorem BayesianSingleItemAuction.PaymentInterimFubiniAssumptions.hasExpectedRevenueInterimPaymentIdentity
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (h : A.PaymentInterimFubiniAssumptions B) :
    A.HasExpectedRevenueInterimPaymentIdentity B := by
  dsimp [
    HasExpectedRevenueInterimPaymentIdentity,
    expectedSellerRevenueInEnvironment,
    expectedPaymentRevenueInEnvironment,
    expectedInterimPaymentRevenue]
  calc
    (∫ t, ∑ i, B.paymentRule t i ∂A.prior)
        = ∑ i, ∫ t, B.paymentRule t i ∂A.prior := by
          simpa using
            (integral_finset_sum (s := Finset.univ)
              (f := fun i t => B.paymentRule t i)
              (fun i _ => h.payment_integrable i))
    _ = ∑ i, ∫ v in 0..A.typeData.omega i,
          B.interimExpectedPayment i v * A.typeDensity i v := by
          exact Finset.sum_congr rfl fun i _ => h.payment_interim_fubini i
