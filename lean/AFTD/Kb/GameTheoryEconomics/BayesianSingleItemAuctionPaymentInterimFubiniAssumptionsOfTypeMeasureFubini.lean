import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeDensity
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimExpectedPayment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionPaymentInterimFubiniAssumptions
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIntegralTypeMeasureEqIntervalIntegralMul
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
# BayesianSingleItemAuction.paymentInterimFubiniAssumptions_of_typeMeasure_fubini

Topic: mechanism_design   Node: 39ec16af6311

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.paymentInterimFubiniAssumptions_of_typeMeasure_fubini`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Build payment-side interim Fubini hypotheses from type-measure Fubini.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- Build payment-side interim Fubini hypotheses from type-measure Fubini. -/
theorem BayesianSingleItemAuction.paymentInterimFubiniAssumptions_of_typeMeasure_fubini
    [Fintype I] {A B : BayesianSingleItemAuction I}
    (hdens_meas :
      ∀ i : I,
        AEMeasurable
          (fun v => ENNReal.ofReal (A.typeDensity i v))
          (volume.restrict (Set.Ioc 0 (A.typeData.omega i))))
    (hdens_ae :
      ∀ i : I,
        ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
          0 ≤ A.typeDensity i v)
    (hpay_int : ∀ i : I, Integrable (fun t => B.paymentRule t i) A.prior)
    (hpay_fubini :
      ∀ i : I,
        (∫ t, B.paymentRule t i ∂A.prior) =
          ∫ v, B.interimExpectedPayment i v ∂A.typeMeasure i) :
    A.PaymentInterimFubiniAssumptions B where
  payment_integrable := hpay_int
  payment_interim_fubini := by
    intro i
    calc
      (∫ t, B.paymentRule t i ∂A.prior)
          = ∫ v, B.interimExpectedPayment i v ∂A.typeMeasure i :=
            hpay_fubini i
      _ = ∫ v in 0..A.typeData.omega i,
            B.interimExpectedPayment i v * A.typeDensity i v := by
            exact A.integral_typeMeasure_eq_intervalIntegral_mul i
              (B.interimExpectedPayment i)
              (hdens_meas i)
              (hdens_ae i)
