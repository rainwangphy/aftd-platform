import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasSameSellingEnvironment
import AFTD.Kb.GameTheoryEconomics.OpponentTypeProfile
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall

/-!
# BayesianSingleItemAuction.HasSameSellingEnvironment.opponentPrior_eq

Topic: mechanism_design   Node: 5f50d8dd9092

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.HasSameSellingEnvironment.opponentPrior_eq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BayesianSingleItemAuction.HasSameSellingEnvironment.opponentPrior_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
theorem BayesianSingleItemAuction.HasSameSellingEnvironment.opponentPrior_eq
    {A B : BayesianSingleItemAuction I}
    (h : A.HasSameSellingEnvironment B) :
    B.opponentPrior = A.opponentPrior :=
  h.2.1
