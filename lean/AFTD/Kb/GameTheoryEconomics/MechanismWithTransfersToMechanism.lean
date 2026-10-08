import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.Mechanism

/-!
# MechanismWithTransfers.toMechanism

Topic: mechanism_design   Node: 7ca3580eb4c2

Provenance: formalization of a published result. Source: EconCSLib, `MechanismWithTransfers.toMechanism`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Transfer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Viewing `MechanismWithTransfers` as a general `Mechanism`. The outcome type is `A × (I → P)` (allocation, payment vector).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [DecidableEq I] {T : I → Type*} {A P V U : Type*} in
variable (M : MechanismWithTransfers I T A P) in
/-- Viewing `MechanismWithTransfers` as a general `Mechanism`. The outcome type is `A × (I → P)` (allocation, payment vector). -/
def MechanismWithTransfers.toMechanism :
    Mechanism I T (A × (I → P)) where
  outcome r := (M.allocationRule r, M.paymentRule r)
