import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasInterimEnvelopeDerivative
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasIntervalIntegrableInterimAllocation
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasInterimEnvelopeFormula
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEquilibriumPayoff
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
# BayesianSingleItemAuction.hasInterimEnvelopeFormula_of_hasInterimEnvelopeDerivative

Topic: mechanism_design   Node: 1e1d744d2f70

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.hasInterimEnvelopeFormula_of_hasInterimEnvelopeDerivative`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The envelope derivative gives the payoff envelope.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- The envelope derivative gives the payoff envelope. -/
theorem BayesianSingleItemAuction.hasInterimEnvelopeFormula_of_hasInterimEnvelopeDerivative
    (A : BayesianSingleItemAuction I)
    (hderiv : A.HasInterimEnvelopeDerivative)
    (hint : A.HasIntervalIntegrableInterimAllocation) :
    A.HasInterimEnvelopeFormula := by
  intro i v_i
  have hFTC :
      ∫ z in 0..v_i, A.interimAllocProb i z =
        A.equilibriumPayoff i v_i - A.equilibriumPayoff i 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := A.equilibriumPayoff i)
      (f' := A.interimAllocProb i)
      (a := 0) (b := v_i)
      (fun x _hx => hderiv i x)
      (hint i 0 v_i)
  rw [hFTC]
  ring
