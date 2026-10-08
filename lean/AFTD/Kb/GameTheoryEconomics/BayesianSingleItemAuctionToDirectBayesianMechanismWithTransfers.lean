import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.DirectBayesianMechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersDirectRevelationAllocationTruthful
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersDirectRevelationPaymentsTruthful
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior

/-!
# BayesianSingleItemAuction.toDirectBayesianMechanismWithTransfers

Topic: mechanism_design   Node: 881a76501985

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.toDirectBayesianMechanismWithTransfers`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

View an incomplete-information single-item auction as the corresponding direct Bayesian mechanism with transfers.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
variable {I : Type*} in
/-- View an incomplete-information single-item auction as the corresponding direct Bayesian mechanism with transfers. -/
def BayesianSingleItemAuction.toDirectBayesianMechanismWithTransfers (A : BayesianSingleItemAuction I) :
    DirectBayesianMechanismWithTransfers I (fun _ => ℝ) (I → ℝ) ℝ where
  prior := A.prior
  prob_prior := A.prob_prior
  allocationRule := A.allocationRule
  paymentRule := A.paymentRule
