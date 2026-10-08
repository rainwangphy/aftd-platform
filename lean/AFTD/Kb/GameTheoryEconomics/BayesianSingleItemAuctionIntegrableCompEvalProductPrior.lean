import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.integrable_comp_eval_productPrior

Topic: mechanism_design   Node: 8ee4412495d7

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.integrable_comp_eval_productPrior`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

BayesianSingleItemAuction.integrable_comp_eval_productPrior
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
theorem BayesianSingleItemAuction.integrable_comp_eval_productPrior [Fintype I]
    (A : BayesianSingleItemAuction I)
    [∀ i : I, IsProbabilityMeasure (A.typeMeasure i)] {i : I} {E : Type*}
    [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Integrable f (A.typeMeasure i)) :
    Integrable (fun t : ∀ _ : I, ℝ => f (t i)) A.productPrior := by
  simpa [productPrior] using
    (integrable_comp_eval (μ := fun j : I => A.typeMeasure j) (i := i) hf)
