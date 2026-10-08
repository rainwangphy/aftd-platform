import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionIntegralTypeMeasureEqIntervalIntegralSmul
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeDensity
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior

/-!
# BayesianSingleItemAuction.integral_typeMeasure_eq_intervalIntegral_mul

Topic: mechanism_design   Node: 8dc01722a48b

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.integral_typeMeasure_eq_intervalIntegral_mul`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Real-valued form of `integral_typeMeasure_eq_intervalIntegral_smul`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- Real-valued form of `integral_typeMeasure_eq_intervalIntegral_smul`. -/
theorem BayesianSingleItemAuction.integral_typeMeasure_eq_intervalIntegral_mul
    (A : BayesianSingleItemAuction I) (i : I) (g : ℝ → ℝ)
    (hmeas :
      AEMeasurable
        (fun v => ENNReal.ofReal (A.typeDensity i v))
        (volume.restrict (Set.Ioc 0 (A.typeData.omega i))))
    (hnonneg :
      ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
        0 ≤ A.typeDensity i v) :
    (∫ v, g v ∂A.typeMeasure i) =
      ∫ v in 0..A.typeData.omega i, g v * A.typeDensity i v := by
  have h :=
    A.integral_typeMeasure_eq_intervalIntegral_smul i g hmeas hnonneg
  calc
    (∫ v, g v ∂A.typeMeasure i)
        = ∫ v in 0..A.typeData.omega i, A.typeDensity i v * g v := by
          simpa [smul_eq_mul] using h
    _ = ∫ v in 0..A.typeData.omega i, g v * A.typeDensity i v := by
          refine intervalIntegral.integral_congr_ae ?_
          filter_upwards with v _hv
          ring
