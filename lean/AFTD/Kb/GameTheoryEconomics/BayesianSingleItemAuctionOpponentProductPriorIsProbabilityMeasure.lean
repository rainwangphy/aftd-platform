import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeMeasure
import AFTD.Kb.GameTheoryEconomics.OpponentTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.opponentProductPrior_isProbabilityMeasure

Topic: mechanism_design   Node: 5fb2b1652ae2

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.opponentProductPrior_isProbabilityMeasure`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BayesianSingleItemAuction.opponentProductPrior_isProbabilityMeasure
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
instance BayesianSingleItemAuction.opponentProductPrior_isProbabilityMeasure [Fintype I] [DecidableEq I]
    (A : BayesianSingleItemAuction I) (i : I)
    [∀ j : I, IsProbabilityMeasure (A.typeMeasure j)] :
    IsProbabilityMeasure (A.opponentProductPrior i) := by
  dsimp [opponentProductPrior]
  infer_instance
