import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersStrategyProfile

/-!
# DirectBayesianMechanismWithTransfers.truthfulStrategy

Topic: mechanism_design   Node: 2a6294896853

Provenance: formalization of a published result. Source: EconCSLib, `DirectBayesianMechanismWithTransfers.truthfulStrategy`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Truthful reporting in a direct Bayesian mechanism with transfers.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)] {A P : Type*} in
/-- Truthful reporting in a direct Bayesian mechanism with transfers. -/
def DirectBayesianMechanismWithTransfers.truthfulStrategy :
    BayesianMechanismWithTransfers.StrategyProfile T T :=
  fun _ => id
