import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersStrategyProfile
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersInducedAllocation
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersInducedPayments

/-!
# BayesianMechanismWithTransfers.exAnteExpectedUtility

Topic: mechanism_design   Node: ed725f52ad91

Provenance: formalization of a published result. Source: EconCSLib, `BayesianMechanismWithTransfers.exAnteExpectedUtility`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Ex-ante expected utility of agent `i` under a strategy profile. The utility rule is supplied externally, as in `MechanismWithTransfers`: it depends on the induced allocation, the induced payments, the realized true type profile, and the agent index.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)] in
variable {M : I → Type*} {A P : Type*} in
/-- Ex-ante expected utility of agent `i` under a strategy profile. The utility rule is supplied externally, as in `MechanismWithTransfers`: it depends on the induced allocation, the induced payments, the realized true type profile, and the agent index. -/
noncomputable def BayesianMechanismWithTransfers.exAnteExpectedUtility
    (B : BayesianMechanismWithTransfers I T M A P)
    (u : A → (I → P) → (∀ i, T i) → I → ℝ)
    (σ : StrategyProfile T M) (i : I) : ℝ :=
  ∫ t, u (B.inducedAllocation σ t) (B.inducedPayments σ t) t i ∂B.prior
