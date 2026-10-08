import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismQuasiLinearValue
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismPayment

/-!
# SingleParameterMechanism.quasiLinearUtility

Topic: mechanism_design   Node: c8212bbf1da9

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.quasiLinearUtility`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Transfer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Quasi-linear utility in the single-parameter setting: `uᵢ(θ, b) = θᵢ * xᵢ(b) - pᵢ(b)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SingleParameterMechanism in
variable {I : Type*} [DecidableEq I] {R : Type*} in
variable (M : SingleParameterMechanism I R) in
/-- Quasi-linear utility in the single-parameter setting: `uᵢ(θ, b) = θᵢ * xᵢ(b) - pᵢ(b)`. -/
def SingleParameterMechanism.quasiLinearUtility [Mul R] [Sub R]
    (b θ : I → R) (i : I) : R :=
  quasiLinearValue (M.allocationRule b) θ i - M.payment b i
