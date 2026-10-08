import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianMechanism
import AFTD.Kb.GameTheoryEconomics.Mechanism

/-!
# BayesianMechanism.toMechanism

Topic: mechanism_design   Node: f5ffb900bac2

Provenance: formalization of a published result. Source: EconCSLib, `BayesianMechanism.toMechanism`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Forget the prior and view a Bayesian mechanism simply as a mechanism on reported messages.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)] in
variable {M : I → Type*} {O : Type*} in
/-- Forget the prior and view a Bayesian mechanism simply as a mechanism on reported messages. -/
def BayesianMechanism.toMechanism (B : BayesianMechanism I T M O) : Mechanism I M O where
  outcome := B.outcome
