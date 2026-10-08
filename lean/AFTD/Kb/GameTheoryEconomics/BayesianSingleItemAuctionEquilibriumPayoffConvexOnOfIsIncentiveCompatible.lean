import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsIncentiveCompatible
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEquilibriumPayoff
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
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
# BayesianSingleItemAuction.equilibriumPayoff_convexOn_of_isIncentiveCompatible

Topic: mechanism_design   Node: a8451348571b

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.equilibriumPayoff_convexOn_of_isIncentiveCompatible`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IC makes truthful payoff convex.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- IC makes truthful payoff convex. -/
theorem BayesianSingleItemAuction.equilibriumPayoff_convexOn_of_isIncentiveCompatible
    (A : BayesianSingleItemAuction I) (hIC : A.IsIncentiveCompatible) (i : I) :
    ConvexOn ℝ Set.univ (A.equilibriumPayoff i) := by
  constructor
  · exact convex_univ
  · intro x _hx y _hy a b ha hb hab
    simp only [smul_eq_mul]
    let m := a * x + b * y
    let Wm := A.equilibriumPayoff i m
    let Qm := A.interimAllocProb i m
    change Wm ≤ a * A.equilibriumPayoff i x + b * A.equilibriumPayoff i y
    have hineq := A.isIncentiveCompatible_iff_equilibriumPayoff_ge.mp hIC
    have hxineq :
        Wm + Qm * (x - m) ≤
          A.equilibriumPayoff i x := by
      simpa [Wm, Qm, m] using hineq i x m
    have hyineq :
        Wm + Qm * (y - m) ≤
          A.equilibriumPayoff i y := by
      simpa [Wm, Qm, m] using hineq i y m
    have hxscaled := mul_le_mul_of_nonneg_left hxineq ha
    have hyscaled := mul_le_mul_of_nonneg_left hyineq hb
    have hsum := add_le_add hxscaled hyscaled
    have hcombo : a * (x - m) + b * (y - m) = 0 := by
      have hm : a * x + b * y = m := rfl
      calc
        a * (x - m) + b * (y - m) = (a * x + b * y) - (a + b) * m := by
          ring
        _ = m - 1 * m := by rw [hm, hab]
        _ = 0 := by ring
    have hleft : a * (Wm + Qm * (x - m)) + b * (Wm + Qm * (y - m)) = Wm := by
      calc
        a * (Wm + Qm * (x - m)) + b * (Wm + Qm * (y - m))
            = (a + b) * Wm + Qm * (a * (x - m) + b * (y - m)) := by
              ring
        _ = Wm := by
              rw [hab, hcombo]
              ring
    nlinarith
