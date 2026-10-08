import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismStrategyProfile

/-!
# BayesianMechanism.inducedMessages

Topic: mechanism_design   Node: 3d6c0739ba66

Provenance: formalization of a published result. Source: EconCSLib, `BayesianMechanism.inducedMessages`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The message profile induced by a true type profile and a strategy profile.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)] in
variable {M : I → Type*} {O : Type*} in
/-- The message profile induced by a true type profile and a strategy profile. -/
def BayesianMechanism.inducedMessages (σ : StrategyProfile T M) (t : ∀ i, T i) : ∀ i, M i :=
  fun i => σ i (t i)
