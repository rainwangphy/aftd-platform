import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasInterimEnvelopeFormula
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimExpectedPayment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEquilibriumPayoff
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimExpectedPaymentEqOfHasInterimPaymentFormulaOfInterimAllocProbEq
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasInterimPaymentFormulaOfHasInterimEnvelopeFormula
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEquilibriumPayoffEqOfHasInterimEnvelopeFormulaOfInterimAllocProbEq
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
# BayesianSingleItemAuction.interimExpectedPayment_eq_and_equilibriumPayoff_eq_of_hasInterimEnvelopeFormula

Topic: mechanism_design   Node: c1ca86c8c464

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.interimExpectedPayment_eq_and_equilibriumPayoff_eq_of_hasInterimEnvelopeFormula`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

[MSZ 12.50] Same `q_i` and zero-type payment give the same interim objects.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- [MSZ 12.50] Same `q_i` and zero-type payment give the same interim objects. -/
theorem BayesianSingleItemAuction.interimExpectedPayment_eq_and_equilibriumPayoff_eq_of_hasInterimEnvelopeFormula
    (A B : BayesianSingleItemAuction I)
    (henvA : A.HasInterimEnvelopeFormula) (henvB : B.HasInterimEnvelopeFormula)
    (i : I)
    (hQ : ∀ z : ℝ, A.interimAllocProb i z = B.interimAllocProb i z)
    (hM0 : A.interimExpectedPayment i 0 = B.interimExpectedPayment i 0)
    (v_i : ℝ) :
    A.interimExpectedPayment i v_i = B.interimExpectedPayment i v_i ∧
      A.equilibriumPayoff i v_i = B.equilibriumPayoff i v_i := by
  constructor
  · exact
      A.interimExpectedPayment_eq_of_hasInterimPaymentFormula_of_interimAllocProb_eq B
        (A.hasInterimPaymentFormula_of_hasInterimEnvelopeFormula henvA)
        (B.hasInterimPaymentFormula_of_hasInterimEnvelopeFormula henvB)
        i hQ hM0 v_i
  · exact
      A.equilibriumPayoff_eq_of_hasInterimEnvelopeFormula_of_interimAllocProb_eq B
        henvA henvB i hQ hM0 v_i
