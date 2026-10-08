import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIsIncentiveCompatible
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionHasInterimEnvelopeFormula
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEquilibriumPayoff
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInterimAllocProb
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionEquilibriumPayoffConvexOnOfIsIncentiveCompatible
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionDerivEquilibriumPayoffEqInterimAllocProbOfIsIncentiveCompatible
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
# BayesianSingleItemAuction.hasInterimEnvelopeFormula_of_isIncentiveCompatible

Topic: mechanism_design   Node: 83db3a43d38f

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.hasInterimEnvelopeFormula_of_isIncentiveCompatible`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

[MSZ 12.49] Payoff envelope from IC.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- [MSZ 12.49] Payoff envelope from IC. -/
theorem BayesianSingleItemAuction.hasInterimEnvelopeFormula_of_isIncentiveCompatible
    (A : BayesianSingleItemAuction I)
    (hIC : A.IsIncentiveCompatible) :
    A.HasInterimEnvelopeFormula := by
  intro i v_i
  let W : ℝ → ℝ := A.equilibriumPayoff i
  let Q : ℝ → ℝ := A.interimAllocProb i
  change W v_i = W 0 + ∫ z in 0..v_i, Q z
  have hconv : ConvexOn ℝ Set.univ W := by
    simpa [W] using A.equilibriumPayoff_convexOn_of_isIncentiveCompatible hIC i
  have hll : LocallyLipschitz W :=
    hconv.locallyLipschitz
  have hll_on : LocallyLipschitzOn (Set.uIcc 0 v_i) W :=
    hll.locallyLipschitzOn
  obtain ⟨K, hK⟩ :=
    LocallyLipschitzOn.exists_lipschitzOnWith_of_compact isCompact_uIcc hll_on
  have hAC : AbsolutelyContinuousOnInterval W 0 v_i :=
    hK.absolutelyContinuousOnInterval
  have hFTC :
      ∫ z in 0..v_i, deriv W z = W v_i - W 0 :=
    hAC.integral_deriv_eq_sub
  have hae_deriv_eq :
      ∀ᵐ z ∂volume, z ∈ Set.uIoc 0 v_i → deriv W z = Q z := by
    filter_upwards [hAC.ae_differentiableAt] with z hdiff hz
    have hdiff_z : DifferentiableAt ℝ W z := hdiff (Set.uIoc_subset_uIcc hz)
    simpa [W, Q] using
      A.deriv_equilibriumPayoff_eq_interimAllocProb_of_isIncentiveCompatible hIC
        (i := i) (v_i := z) hdiff_z
  have hcongr :
      ∫ z in 0..v_i, deriv W z = ∫ z in 0..v_i, Q z :=
    intervalIntegral.integral_congr_ae hae_deriv_eq
  calc
    W v_i = W 0 + ∫ z in 0..v_i, deriv W z := by
      linarith
    _ = W 0 + ∫ z in 0..v_i, Q z := by
      rw [hcongr]
