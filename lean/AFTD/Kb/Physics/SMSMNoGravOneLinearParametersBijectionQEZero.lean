import AFTD.Prelude
import AFTD.Kb.Physics.SMSMNoGravOneLinearParameters
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMChargesQ
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.SMSMNoGrav
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersBijection
import AFTD.Kb.Physics.SMChargesE
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.SMACCsAccQuad
import AFTD.Kb.Physics.SMACCsAccCube
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.ACCSystemLinearLinSolsExt

/-!
# SM.SMNoGrav.One.linearParameters.bijectionQEZero

Topic: quantum_field_theory   Node: db42cfca5652

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.One.linearParameters.bijectionQEZero`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/One/LinearParameterization.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The bijection between the linear parameters and `(SMNoGrav 1).LinSols` in the special case when Q and E are both not zero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMCharges in
open SMACCs in
open BigOperators in
/-- The bijection between the linear parameters and `(SMNoGrav 1).LinSols` in the special case when Q and E are both not zero. -/
def SM.SMNoGrav.One.linearParameters.bijectionQEZero : {S : linearParameters // S.Q' ≠ 0 ∧ S.E' ≠ 0} ≃
    {S : (SMNoGrav 1).LinSols // Q S.val (0 : Fin 1) ≠ 0 ∧ E S.val (0 : Fin 1) ≠ 0} where
  toFun S := ⟨bijection S, S.2⟩
  invFun S := ⟨bijection.symm S, S.2⟩
  left_inv S := Subtype.ext (bijection.left_inv S.1)
  right_inv S := Subtype.ext (bijection.right_inv S.1)
