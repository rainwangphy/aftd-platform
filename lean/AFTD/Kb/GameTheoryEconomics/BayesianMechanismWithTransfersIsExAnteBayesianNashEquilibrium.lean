import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersStrategyProfile
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismIsMeasurableStrategyProfile
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersExAnteExpectedUtility
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersDeviate
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.Deviate

/-!
# BayesianMechanismWithTransfers.IsExAnteBayesianNashEquilibrium

Topic: mechanism_design   Node: 81d3b7c07e1b

Provenance: formalization of a published result. Source: EconCSLib, `BayesianMechanismWithTransfers.IsExAnteBayesianNashEquilibrium`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An ex-ante Bayesian Nash equilibrium of a transfer mechanism. No agent can improve their ex-ante expected utility by replacing their reporting rule with any other measurable pure type-contingent reporting rule. This is the ex-ante notion: expectations are taken under the full prior, not conditional on agent `i`'s realized type. The standard interim BNE notion from mechanism design is a natural future extension.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)] in
variable {M : I → Type*} {A P : Type*} in
/-- An ex-ante Bayesian Nash equilibrium of a transfer mechanism. No agent can improve their ex-ante expected utility by replacing their reporting rule with any other measurable pure type-contingent reporting rule. This is the ex-ante notion: expectations are taken under the full prior, not conditional on agent `i`'s realized type. The standard interim BNE notion from mechanism design is a natural future extension. -/
def BayesianMechanismWithTransfers.IsExAnteBayesianNashEquilibrium
    [DecidableEq I]
    [∀ i, MeasurableSpace (M i)]
    (B : BayesianMechanismWithTransfers I T M A P)
    (u : A → (I → P) → (∀ i, T i) → I → ℝ)
    (σ : StrategyProfile T M) : Prop :=
  BayesianMechanism.IsMeasurableStrategyProfile σ ∧
    ∀ (i : I) (τ : T i → M i), Measurable τ →
      B.exAnteExpectedUtility u (deviate σ i τ) i ≤
        B.exAnteExpectedUtility u σ i
