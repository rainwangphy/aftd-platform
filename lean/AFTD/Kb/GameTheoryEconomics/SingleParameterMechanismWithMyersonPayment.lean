import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismMyersonPayment

/-!
# SingleParameterMechanism.withMyersonPayment

Topic: mechanism_design   Node: 78173ffaf5d1

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.withMyersonPayment`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Myerson.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The single-parameter mechanism obtained by equipping an allocation rule with its canonical Myerson payment rule.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SingleParameterMechanism in
variable {I : Type*} in
/-- The single-parameter mechanism obtained by equipping an allocation rule with its canonical Myerson payment rule. -/
noncomputable def SingleParameterMechanism.withMyersonPayment
    [DecidableEq I]
    (x : (I → ℝ) → I → ℝ) : SingleParameterMechanism I ℝ where
  allocationRule := x
  paymentRule := myersonPayment x
