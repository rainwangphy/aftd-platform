import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasInterimEnvelopeFormula
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasInterimPaymentFormula
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimExpectedPayment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEquilibriumPayoff
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimQuasiLinearUtility
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
# BayesianSingleItemAuction.hasInterimPaymentFormula_of_hasInterimEnvelopeFormula

Topic: mechanism_design   Node: 8648960b4b99

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.hasInterimPaymentFormula_of_hasInterimEnvelopeFormula`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The payoff envelope implies the payment identity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- The payoff envelope implies the payment identity. -/
theorem BayesianSingleItemAuction.hasInterimPaymentFormula_of_hasInterimEnvelopeFormula
    (A : BayesianSingleItemAuction I) (henv : A.HasInterimEnvelopeFormula) :
    A.HasInterimPaymentFormula := by
  intro i v_i
  calc
    A.interimExpectedPayment i v_i
        = A.interimAllocProb i v_i * v_i - A.equilibriumPayoff i v_i := by
          rw [equilibriumPayoff, interimQuasiLinearUtility]
          ring
    _ = A.interimAllocProb i v_i * v_i -
          (A.equilibriumPayoff i 0 + ∫ z in 0..v_i, A.interimAllocProb i z) := by
          rw [henv i v_i]
    _ = A.interimExpectedPayment i 0 + A.interimAllocProb i v_i * v_i -
          ∫ z in 0..v_i, A.interimAllocProb i z := by
          rw [equilibriumPayoff, interimQuasiLinearUtility]
          ring
