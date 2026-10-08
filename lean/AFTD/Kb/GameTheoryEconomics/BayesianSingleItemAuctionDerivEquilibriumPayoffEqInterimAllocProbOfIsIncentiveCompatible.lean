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
# BayesianSingleItemAuction.deriv_equilibriumPayoff_eq_interimAllocProb_of_isIncentiveCompatible

Topic: mechanism_design   Node: a45efcab2211

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.deriv_equilibriumPayoff_eq_interimAllocProb_of_isIncentiveCompatible`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

At differentiable types, `U_i' = q_i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- At differentiable types, `U_i' = q_i`. -/
theorem BayesianSingleItemAuction.deriv_equilibriumPayoff_eq_interimAllocProb_of_isIncentiveCompatible
    (A : BayesianSingleItemAuction I) (hIC : A.IsIncentiveCompatible)
    {i : I} {v_i : ℝ}
    (hdiff : DifferentiableAt ℝ (A.equilibriumPayoff i) v_i) :
    deriv (A.equilibriumPayoff i) v_i = A.interimAllocProb i v_i := by
  let q := A.interimAllocProb i v_i
  have hineq := A.isIncentiveCompatible_iff_equilibriumPayoff_ge.mp hIC
  have hmin :
      IsMinOn (fun x : ℝ => A.equilibriumPayoff i x - q * x) Set.univ v_i := by
    rw [isMinOn_univ_iff]
    intro x
    have hxineq : A.equilibriumPayoff i x ≥ A.equilibriumPayoff i v_i + q * (x - v_i) := by
      simpa [q] using hineq i x v_i
    nlinarith
  have hlocal : IsLocalMin (fun x : ℝ => A.equilibriumPayoff i x - q * x) v_i :=
    hmin.isLocalMin (by simp)
  have hderiv :
      HasDerivAt (fun x : ℝ => A.equilibriumPayoff i x - q * x)
        (deriv (A.equilibriumPayoff i) v_i - q) v_i := by
    exact hdiff.hasDerivAt.sub (hasDerivAt_const_mul (x := v_i) q)
  have hzero : deriv (A.equilibriumPayoff i) v_i - q = 0 :=
    hlocal.hasDerivAt_eq_zero hderiv
  simpa [q] using sub_eq_zero.mp hzero
