import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersStrategyProfile
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersIsExAnteBayesianNashEquilibrium
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersDirectRevelation
import AFTD.Kb.GameTheoryEconomics.DirectBayesianMechanismWithTransfersTruthfulStrategy
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersDirectRevelationAllocationTruthful
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersDirectRevelationPaymentsTruthful

/-!
# BayesianMechanismWithTransfers.ExAnteRevelationPrincipleConclusion

Topic: mechanism_design   Node: 20125e927b40

Provenance: formalization of a published result. Source: EconCSLib, `BayesianMechanismWithTransfers.ExAnteRevelationPrincipleConclusion`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The revelation-principle target property attached to a strategy profile. This packages the statement we will eventually want to prove: if `σ` is an equilibrium of the indirect mechanism, then truthful reporting is a Bayesian equilibrium of the induced direct mechanism.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)] in
variable {M : I → Type*} {A P : Type*} in
/-- The revelation-principle target property attached to a strategy profile. This packages the statement we will eventually want to prove: if `σ` is an equilibrium of the indirect mechanism, then truthful reporting is a Bayesian equilibrium of the induced direct mechanism. -/
def BayesianMechanismWithTransfers.ExAnteRevelationPrincipleConclusion
    [DecidableEq I]
    [∀ i, MeasurableSpace (T i)]
    [∀ i, MeasurableSpace (M i)]
    (B : BayesianMechanismWithTransfers I T M A P)
    (u : A → (I → P) → (∀ i, T i) → I → ℝ)
    (σ : StrategyProfile T M) : Prop :=
  (B.directRevelation σ).IsExAnteBayesianNashEquilibrium u
    DirectBayesianMechanismWithTransfers.truthfulStrategy

-- Omit the variable-scope `MeasurableSpace (T i)` so that the type and message
-- measurability instances appear together in the explicit binder list below.
