import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismQuasiLinearUtility
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfersQuasiLinearUtility
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.Tcs.V

/-!
# SingleParameterMechanism.quasiLinearUtility_eq_transferQuasiLinearUtility

Topic: mechanism_design   Node: a86fe6caf8fc

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.quasiLinearUtility_eq_transferQuasiLinearUtility`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Transfer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The single-parameter quasi-linear utility is the specialization of the generic transfer-mechanism quasi-linear utility to `val a θ i = θᵢ * aᵢ` and identity payment embedding.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SingleParameterMechanism in
variable {I : Type*} [DecidableEq I] {R : Type*} in
variable (M : SingleParameterMechanism I R) in
omit [DecidableEq I] in
/-- The single-parameter quasi-linear utility is the specialization of the generic transfer-mechanism quasi-linear utility to `val a θ i = θᵢ * aᵢ` and identity payment embedding. -/
lemma SingleParameterMechanism.quasiLinearUtility_eq_transferQuasiLinearUtility [Mul R] [Sub R]
    (b θ : I → R) (i : I) :
    M.quasiLinearUtility b θ i =
      MechanismWithTransfers.quasiLinearUtility
        (I := I) (T := fun _ => R) (A := I → R) (P := R) (V := R) (U := R)
        ({ allocationRule := M.allocationRule
           paymentRule := M.paymentRule } :
          MechanismWithTransfers I (fun _ => R) (I → R) R)
        (fun a types j => types j * a j)
        id id b θ i := rfl
