import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfersStrategyProfile
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismInducedMessages

/-!
# BayesianMechanismWithTransfers.inducedPayments

Topic: mechanism_design   Node: e4788601dc51

Provenance: formalization of a published result. Source: EconCSLib, `BayesianMechanismWithTransfers.inducedPayments`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The payment vector induced by a strategy profile and a realized type profile.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)] in
variable {M : I → Type*} {A P : Type*} in
/-- The payment vector induced by a strategy profile and a realized type profile. -/
def BayesianMechanismWithTransfers.inducedPayments
    (B : BayesianMechanismWithTransfers I T M A P)
    (σ : StrategyProfile T M) (t : ∀ i, T i) : I → P :=
  B.paymentRule (BayesianMechanism.inducedMessages σ t)
