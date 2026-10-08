import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismStrategyProfile

/-!
# BayesianMechanismWithTransfers.StrategyProfile

Topic: mechanism_design   Node: e5db3b7caa75

Provenance: formalization of a published result. Source: EconCSLib, `BayesianMechanismWithTransfers.StrategyProfile`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A pure reporting strategy profile for a Bayesian transfer mechanism.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)] in
variable {M : I → Type*} {A P : Type*} in
/-- A pure reporting strategy profile for a Bayesian transfer mechanism. -/
abbrev BayesianMechanismWithTransfers.StrategyProfile (T : I → Type*) (M : I → Type*) :=
  BayesianMechanism.StrategyProfile T M
