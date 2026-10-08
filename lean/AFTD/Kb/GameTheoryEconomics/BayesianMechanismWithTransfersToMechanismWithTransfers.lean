import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BayesianMechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers

/-!
# BayesianMechanismWithTransfers.toMechanismWithTransfers

Topic: mechanism_design   Node: e25874a2d4ab

Provenance: formalization of a published result. Source: EconCSLib, `BayesianMechanismWithTransfers.toMechanismWithTransfers`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/MechBayesian.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Forget the Bayesian prior and recover the underlying transfer mechanism on reported messages.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
variable {I : Type*} {T : I → Type*} [∀ i, MeasurableSpace (T i)] in
variable {M : I → Type*} {A P : Type*} in
/-- Forget the Bayesian prior and recover the underlying transfer mechanism on reported messages. -/
def BayesianMechanismWithTransfers.toMechanismWithTransfers
    (B : BayesianMechanismWithTransfers I T M A P) :
    MechanismWithTransfers I M A P where
  allocationRule := B.allocationRule
  paymentRule := B.paymentRule
