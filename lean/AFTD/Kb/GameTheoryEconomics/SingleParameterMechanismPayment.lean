import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers

/-!
# SingleParameterMechanism.payment

Topic: mechanism_design   Node: c912e472cfc0

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.payment`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Transfer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The payment vector induced by a bid profile in a single-parameter mechanism. This is just the inherited `MechanismWithTransfers.paymentRule`, restated with single-parameter terminology.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [DecidableEq I] {R : Type*} in
variable (M : SingleParameterMechanism I R) in
/-- The payment vector induced by a bid profile in a single-parameter mechanism. This is just the inherited `MechanismWithTransfers.paymentRule`, restated with single-parameter terminology. -/
abbrev SingleParameterMechanism.payment (b : I → R) : I → R :=
  M.paymentRule b
