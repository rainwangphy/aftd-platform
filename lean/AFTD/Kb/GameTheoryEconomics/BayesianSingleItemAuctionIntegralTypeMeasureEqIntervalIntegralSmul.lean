import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeDensity
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionTypeMeasure
import AFTD.Kb.GameTheoryEconomics.TypeCDF
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProductPriorIsProbabilityMeasure
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionOpponentProductPriorIsProbabilityMeasure
import AFTD.Kb.Tcs.G

/-!
# BayesianSingleItemAuction.integral_typeMeasure_eq_intervalIntegral_smul

Topic: mechanism_design   Node: 787447ac3d81

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.integral_typeMeasure_eq_intervalIntegral_smul`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Integral against `typeMeasure` as an interval integral.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BayesianSingleItemAuction in
open MeasureTheory in
variable {I : Type*} in
/-- Integral against `typeMeasure` as an interval integral. -/
theorem BayesianSingleItemAuction.integral_typeMeasure_eq_intervalIntegral_smul
    (A : BayesianSingleItemAuction I) (i : I) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℝ → E)
    (hmeas :
      AEMeasurable
        (fun v => ENNReal.ofReal (A.typeDensity i v))
        (volume.restrict (Set.Ioc 0 (A.typeData.omega i))))
    (hnonneg :
      ∀ᵐ v ∂(volume.restrict (Set.Ioc 0 (A.typeData.omega i))),
        0 ≤ A.typeDensity i v) :
    (∫ v, g v ∂A.typeMeasure i) =
      ∫ v in 0..A.typeData.omega i, A.typeDensity i v • g v := by
  let s := Set.Ioc (0 : ℝ) (A.typeData.omega i)
  have htop :
      ∀ᵐ v ∂(volume.restrict s),
        ENNReal.ofReal (A.typeDensity i v) < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  calc
    (∫ v, g v ∂A.typeMeasure i)
        = ∫ v, (ENNReal.ofReal (A.typeDensity i v)).toReal • g v
            ∂volume.restrict s := by
          simpa [typeMeasure, s] using
            (integral_withDensity_eq_integral_toReal_smul₀
              (μ := volume.restrict s) hmeas htop g)
    _ = ∫ v in s, A.typeDensity i v • g v ∂volume := by
          refine integral_congr_ae ?_
          filter_upwards [hnonneg] with v hv
          rw [ENNReal.toReal_ofReal hv]
    _ = ∫ v in 0..A.typeData.omega i, A.typeDensity i v • g v := by
          exact (intervalIntegral.integral_of_le (A.typeData.cdf i).omega_nonneg).symm
