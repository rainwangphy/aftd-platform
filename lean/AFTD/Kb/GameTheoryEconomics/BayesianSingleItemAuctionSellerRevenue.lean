import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall

/-!
# BayesianSingleItemAuction.sellerRevenue

Topic: mechanism_design   Node: 772733dfa53e

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.sellerRevenue`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Seller revenue at a report profile.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
variable {I : Type*} in
/-- Seller revenue at a report profile. -/
noncomputable def BayesianSingleItemAuction.sellerRevenue [Fintype I]
    (A : BayesianSingleItemAuction I) (t : ∀ _ : I, ℝ) : ℝ :=
  ∑ i, A.paymentRule t i
