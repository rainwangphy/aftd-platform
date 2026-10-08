import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.BayesianMechanism

/-!
# BayesianMechanismWithTransfers.toBayesianMechanism

Topic: mechanism_design   Node: ba3ba7a973cd

Provenance: formalization of a published result. Source: EconCSLib, `BayesianMechanismWithTransfers.toBayesianMechanism`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Forget the transfer decomposition and recover the corresponding Bayesian mechanism with outcome space `A × (I → P)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)] in
variable {M : I → Type*} {A P : Type*} in
/-- Forget the transfer decomposition and recover the corresponding Bayesian mechanism with outcome space `A × (I → P)`. -/
def BayesianMechanismWithTransfers.toBayesianMechanism
    (B : BayesianMechanismWithTransfers I T M A P) :
    BayesianMechanism I T M (A × (I → P)) where
  prior := B.prior
  prob_prior := B.prob_prior
  outcome r := (B.allocationRule r, B.paymentRule r)
