import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsIncentiveCompatible
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEquilibriumPayoff
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasInterimEnvelopeDerivative
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionDerivEquilibriumPayoffEqInterimAllocProbOfIsIncentiveCompatible
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
# BayesianSingleItemAuction.hasInterimEnvelopeDerivative_of_isIncentiveCompatible_of_equilibriumPayoff_differentiable

Topic: mechanism_design   Node: a95e4181817a

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.hasInterimEnvelopeDerivative_of_isIncentiveCompatible_of_equilibriumPayoff_differentiable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IC and differentiability give the envelope derivative.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- IC and differentiability give the envelope derivative. -/
theorem BayesianSingleItemAuction.hasInterimEnvelopeDerivative_of_isIncentiveCompatible_of_equilibriumPayoff_differentiable
    (A : BayesianSingleItemAuction I) (hIC : A.IsIncentiveCompatible)
    (hdiff : ∀ (i : I) (v_i : ℝ), DifferentiableAt ℝ (A.equilibriumPayoff i) v_i) :
    A.HasInterimEnvelopeDerivative := by
  intro i v_i
  have hderiv := (hdiff i v_i).hasDerivAt
  have hderiv_eq :
      deriv (A.equilibriumPayoff i) v_i = A.interimAllocProb i v_i :=
    A.deriv_equilibriumPayoff_eq_interimAllocProb_of_isIncentiveCompatible
      hIC (hdiff i v_i)
  simpa [hderiv_eq] using hderiv
