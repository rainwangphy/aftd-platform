import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.DirectBayesianMechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionToDirectBayesianMechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersDirectRevelationAllocationTruthful
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersDirectRevelationPaymentsTruthful
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior

/-!
# BayesianSingleItemAuction.instCoeDirectBayesianMechanismWithTransfersRealForall

Topic: mechanism_design   Node: 6945e862c948

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.instCoeDirectBayesianMechanismWithTransfersRealForall`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BayesianSingleItemAuction.instCoeDirectBayesianMechanismWithTransfersRealForall
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
instance BayesianSingleItemAuction.instCoeDirectBayesianMechanismWithTransfersRealForall : Coe (BayesianSingleItemAuction I)
    (DirectBayesianMechanismWithTransfers I (fun _ => ℝ) (I → ℝ) ℝ) where
  coe := toDirectBayesianMechanismWithTransfers
