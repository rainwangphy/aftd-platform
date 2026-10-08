import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersStrategyProfile
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersInducedAllocation
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersInducedPayments

/-!
# BayesianMechanismWithTransfers.IntegrableExAnteUtility

Topic: mechanism_design   Node: 15a01e92e922

Provenance: formalization of a published result. Source: EconCSLib, `BayesianMechanismWithTransfers.IntegrableExAnteUtility`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Integrability of ex-ante utilities for agent `i` under a strategy profile.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)] in
variable {M : I → Type*} {A P : Type*} in
/-- Integrability of ex-ante utilities for agent `i` under a strategy profile. -/
def BayesianMechanismWithTransfers.IntegrableExAnteUtility
    (B : BayesianMechanismWithTransfers I T M A P)
    (u : A → (I → P) → (∀ i, T i) → I → ℝ)
    (σ : StrategyProfile T M) (i : I) : Prop :=
  Integrable (fun t => u (B.inducedAllocation σ t) (B.inducedPayments σ t) t i) B.prior
