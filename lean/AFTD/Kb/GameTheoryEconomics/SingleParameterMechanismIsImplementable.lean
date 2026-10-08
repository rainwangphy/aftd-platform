import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsDSIC
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# SingleParameterMechanism.IsImplementable

Topic: mechanism_design   Node: c6ad2541f23f

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.IsImplementable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Transfer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An allocation rule is implementable if there exists some payment rule such that the resulting single-parameter mechanism is DSIC.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SingleParameterMechanism in
variable {I : Type*} [DecidableEq I] {R : Type*} in
variable (M : SingleParameterMechanism I R) in
/-- An allocation rule is implementable if there exists some payment rule such that the resulting single-parameter mechanism is DSIC. -/
def SingleParameterMechanism.IsImplementable [Mul R] [Sub R] [Preorder R]
    (x : (I → R) → I → R) : Prop :=
  ∃ p : (I → R) → I → R,
    ( { allocationRule := x
        paymentRule := p } : SingleParameterMechanism I R).IsDSIC
