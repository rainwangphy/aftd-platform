import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasIndependentTypePriors
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPrior
import AFTD.Kb.GameTheoryEconomics.OpponentTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIntegralCompEvalProductPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.integral_comp_eval_prior_of_hasIndependentTypePriors

Topic: mechanism_design   Node: d00c1e349720

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.integral_comp_eval_prior_of_hasIndependentTypePriors`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BayesianSingleItemAuction.integral_comp_eval_prior_of_hasIndependentTypePriors
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
theorem BayesianSingleItemAuction.integral_comp_eval_prior_of_hasIndependentTypePriors
    [Fintype I] [DecidableEq I] (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)]
    (h : A.HasIndependentTypePriors) {i : I} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    (hf : AEStronglyMeasurable f (A.typeMeasure i)) :
    (∫ t : ∀ _ : I, ℝ, f (t i) ∂A.prior) =
      ∫ v, f v ∂A.typeMeasure i := by
  rw [h.1]
  exact A.integral_comp_eval_productPrior hf
