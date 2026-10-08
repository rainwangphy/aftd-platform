import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsIncentiveCompatible
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEquilibriumPayoff
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsIncentiveCompatibleIffEquilibriumPayoffGe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionUpdateReportProfileSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivApplyFst
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivApplySnd
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileSplitMeasurableEquivSymmApply
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionExpectedSellerRevenueInEnvironmentSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure

/-!
# BayesianSingleItemAuction.interimAllocProb_mono_of_isIncentiveCompatible

Topic: mechanism_design   Node: 31a4c9c7f7e6

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.interimAllocProb_mono_of_isIncentiveCompatible`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IC implies monotonicity of `q_i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- IC implies monotonicity of `q_i`. -/
theorem BayesianSingleItemAuction.interimAllocProb_mono_of_isIncentiveCompatible
    (A : BayesianSingleItemAuction I) (hIC : A.IsIncentiveCompatible) (i : I) :
    Monotone (A.interimAllocProb i) := by
  rw [Monotone]
  intro x y hxy
  by_cases hlt : x < y
  · have hineq := (A.isIncentiveCompatible_iff_equilibriumPayoff_ge.mp hIC)
    have h1 :
        A.equilibriumPayoff i x + A.interimAllocProb i x * (y - x) ≤
          A.equilibriumPayoff i y := by
      exact hineq i y x
    have h2 :
        A.equilibriumPayoff i y + A.interimAllocProb i y * (x - y) ≤
          A.equilibriumPayoff i x := by
      exact hineq i x y
    have hprod :
        (A.interimAllocProb i x - A.interimAllocProb i y) * (y - x) ≤ 0 := by
      nlinarith
    have hpos : 0 < y - x := sub_pos.mpr hlt
    nlinarith
  · have hEq : x = y := le_antisymm hxy (le_of_not_gt hlt)
    simp [hEq]
