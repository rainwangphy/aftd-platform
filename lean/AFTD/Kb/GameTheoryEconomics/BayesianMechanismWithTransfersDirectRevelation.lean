import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersStrategyProfile
import AFTD.Kb.GameTheoryEconomics.DirectBayesianMechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersInducedAllocation
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersInducedPayments

/-!
# BayesianMechanismWithTransfers.directRevelation

Topic: mechanism_design   Node: 13ade8a6526e

Provenance: formalization of a published result. Source: EconCSLib, `BayesianMechanismWithTransfers.directRevelation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The direct-revelation mechanism induced by an indirect mechanism and a strategy profile. An agent reports their type directly; the mechanism then feeds these reports through the original equilibrium reporting strategies and applies the original allocation and payment rules. This is the standard object behind the revelation principle.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)] in
variable {M : I → Type*} {A P : Type*} in
/-- The direct-revelation mechanism induced by an indirect mechanism and a strategy profile. An agent reports their type directly; the mechanism then feeds these reports through the original equilibrium reporting strategies and applies the original allocation and payment rules. This is the standard object behind the revelation principle. -/
def BayesianMechanismWithTransfers.directRevelation
    (B : BayesianMechanismWithTransfers I T M A P)
    (σ : StrategyProfile T M) :
    DirectBayesianMechanismWithTransfers I T A P where
  prior := B.prior
  prob_prior := B.prob_prior
  allocationRule t := B.inducedAllocation σ t
  paymentRule t := B.inducedPayments σ t
