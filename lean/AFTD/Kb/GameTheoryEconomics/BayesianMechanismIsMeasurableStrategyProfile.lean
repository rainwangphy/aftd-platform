import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismStrategyProfile

/-!
# BayesianMechanism.IsMeasurableStrategyProfile

Topic: mechanism_design   Node: e452d3b5eaca

Provenance: formalization of a published result. Source: EconCSLib, `BayesianMechanism.IsMeasurableStrategyProfile`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A measurable strategy profile for all agents in an incomplete-information mechanism.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)] in
variable {M : I → Type*} {O : Type*} in
/-- A measurable strategy profile for all agents in an incomplete-information mechanism. -/
def BayesianMechanism.IsMeasurableStrategyProfile
    [∀ i, MeasurableSpace (M i)]
    (σ : StrategyProfile T M) : Prop :=
  ∀ i, Measurable (σ i)
