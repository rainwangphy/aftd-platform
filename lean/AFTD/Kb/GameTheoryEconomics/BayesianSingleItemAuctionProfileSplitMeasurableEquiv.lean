import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OpponentTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsert
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionUpdateReportProfileSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.profileSplitMeasurableEquiv

Topic: mechanism_design   Node: f677bf4e7b89

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.profileSplitMeasurableEquiv`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Split a profile into coordinate `i` and its opponents.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- Split a profile into coordinate `i` and its opponents. -/
noncomputable def BayesianSingleItemAuction.profileSplitMeasurableEquiv
    (i : I) : (∀ _ : I, ℝ) ≃ᵐ ℝ × OpponentTypeProfile I i where
  toFun t := (t i, fun j => t j)
  invFun p := reportProfile i p.1 p.2
  left_inv := by
    intro t
    funext j
    by_cases hji : j = i
    · subst hji
      simp
    · simp [reportProfile, hji]
  right_inv := by
    rintro ⟨v, t⟩
    ext j
    · simp
    · simp [reportProfile, j.property]
  measurable_toFun := (measurable_pi_apply i).prodMk <|
    measurable_pi_iff.2 fun j => measurable_pi_apply j.1
  measurable_invFun := measurable_pi_iff.2 fun j => by
    by_cases hji : j = i
    · subst hji
      simpa using measurable_fst
    · simpa [reportProfile, hji, Function.comp_def] using
        (measurable_pi_apply (⟨j, hji⟩ : {j // j ≠ i})).comp measurable_snd
