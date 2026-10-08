import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersStrategyProfile
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismStrategy
import AFTD.Kb.GameTheoryEconomics.Deviate

/-!
# BayesianMechanismWithTransfers.deviate

Topic: mechanism_design   Node: 7c3c07132181

Provenance: formalization of a published result. Source: EconCSLib, `BayesianMechanismWithTransfers.deviate`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Deviating from a strategy profile at one agent.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)] in
variable {M : I → Type*} {A P : Type*} in
/-- Deviating from a strategy profile at one agent. -/
def BayesianMechanismWithTransfers.deviate
    [DecidableEq I]
    (σ : StrategyProfile T M) (i : I) (τ : T i → M i) :
    StrategyProfile T M :=
  Function.update σ i τ
