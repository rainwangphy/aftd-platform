import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasIntegrableInterimObjects
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsDSIC
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsIncentiveCompatible
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasIntegrableInterimAllocation
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasIntegrableInterimPayment
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimQuasiLinearUtility
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEquilibriumPayoff
import AFTD.Kb.GameTheoryEconomics.OpponentTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimQuasiLinearUtilityIntegrand
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIntegralInterimQuasiLinearUtilityIntegrandEq
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIntegrableInterimQuasiLinearUtilityIntegrand
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimQuasiLinearUtilityIntegrandLeOfIsDSIC
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
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
# BayesianSingleItemAuction.isIncentiveCompatible_of_isDSIC

Topic: mechanism_design   Node: bca1da6a0410

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.isIncentiveCompatible_of_isDSIC`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

DSIC implies interim IC under interim integrability.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- DSIC implies interim IC under interim integrability. -/
theorem BayesianSingleItemAuction.isIncentiveCompatible_of_isDSIC
    [DecidableEq I] (A : BayesianSingleItemAuction I)
    (hint : A.HasIntegrableInterimObjects) (hdsic : A.IsDSIC) :
    A.IsIncentiveCompatible := by
  intro i t_i z_i
  rcases hint with ⟨hQ, hM⟩
  have hz := A.integral_interimQuasiLinearUtilityIntegrand_eq hQ hM i t_i z_i
  have ht := A.integral_interimQuasiLinearUtilityIntegrand_eq hQ hM i t_i t_i
  rw [equilibriumPayoff, ← hz, ← ht]
  exact integral_mono
    (A.integrable_interimQuasiLinearUtilityIntegrand hQ hM i t_i z_i)
    (A.integrable_interimQuasiLinearUtilityIntegrand hQ hM i t_i t_i)
    (fun t => A.interimQuasiLinearUtilityIntegrand_le_of_isDSIC hdsic i t_i z_i t)
