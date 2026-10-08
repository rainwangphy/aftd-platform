import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuction
import AFTD.Kb.GameTheoryEconomics.TypeCDF
import AFTD.Kb.GameTheoryEconomics.ContinuousTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstIsProbabilityMeasureOpponentTypeProfileOpponentPrior
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionInstCoeDirectBayesianMechanismWithTransfersRealForall
import AFTD.Kb.Tcs.F

/-!
# BayesianSingleItemAuction.typeDensity

Topic: mechanism_design   Node: dce2a9252e3a

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.typeDensity`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Agent `i`'s one-dimensional density, defined as the derivative of the stored CDF `Fᵢ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
variable {I : Type*} in
/-- Agent `i`'s one-dimensional density, defined as the derivative of the stored CDF `Fᵢ`. -/
noncomputable def BayesianSingleItemAuction.typeDensity (A : BayesianSingleItemAuction I) (i : I) : ℝ → ℝ :=
  deriv (A.typeData.cdf i).cdf
