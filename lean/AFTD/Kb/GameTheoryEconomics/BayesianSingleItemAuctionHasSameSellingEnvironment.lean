import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.OpponentTypeProfile
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall

/-!
# BayesianSingleItemAuction.HasSameSellingEnvironment

Topic: mechanism_design   Node: ef4e2a56bd77

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.HasSameSellingEnvironment`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Auctions over the same Bayesian selling environment.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
variable {I : Type*} in
/-- Auctions over the same Bayesian selling environment. -/
def BayesianSingleItemAuction.HasSameSellingEnvironment
    (A B : BayesianSingleItemAuction I) : Prop :=
  B.prior = A.prior ∧
    B.opponentPrior = A.opponentPrior ∧
      B.typeData = A.typeData
