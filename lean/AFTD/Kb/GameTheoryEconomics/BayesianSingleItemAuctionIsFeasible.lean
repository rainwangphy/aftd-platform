import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsAllocFeasible
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionRespectsSingleItemCapacity
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall

/-!
# BayesianSingleItemAuction.IsFeasible

Topic: mechanism_design   Node: 6b395ea34d9e

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.IsFeasible`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Feasibility for a probabilistic single-item auction: * each winning probability lies in `[0,1]` * the total allocation probability is at most `1`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- Feasibility for a probabilistic single-item auction: * each winning probability lies in `[0,1]` * the total allocation probability is at most `1` -/
def BayesianSingleItemAuction.IsFeasible [Fintype I] (A : BayesianSingleItemAuction I) : Prop :=
  A.IsAllocFeasible ∧ A.RespectsSingleItemCapacity
