import AFTD.Prelude
import AFTD.Kb.Physics.SMSMNoGravOneLinearParameters
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMACCsAccSU3
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersAsCharges
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.SMChargesToSpeciesEquiv
import AFTD.Kb.Physics.SMChargesQ
import AFTD.Kb.Physics.SMChargesSumSMSpeciesNumberChargesOne
import AFTD.Kb.Physics.SMChargesU
import AFTD.Kb.Physics.SMChargesD
import AFTD.Kb.Physics.SMChargesToSpecies
import AFTD.Kb.Physics.SMChargesToSpeciesApplyEq
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.SMSMNoGrav
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersSpeciesVal
import AFTD.Kb.Physics.SMACCsAccSU2
import AFTD.Kb.Physics.SMChargesL
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersToSpeciesApplyAsCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.SMSMNoGravChargeToLinear
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

/-!
# SM.SMNoGrav.One.linearParameters.asLinear

Topic: quantum_field_theory   Node: 17fbd103d420

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.One.linearParameters.asLinear`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/One/LinearParameterization.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The map from the linear parameters to elements of `(SMNoGrav 1).LinSols`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMCharges in
open SMACCs in
open BigOperators in
/-- The map from the linear parameters to elements of `(SMNoGrav 1).LinSols`. -/
def SM.SMNoGrav.One.linearParameters.asLinear (S : linearParameters) : (SMNoGrav 1).LinSols :=
  chargeToLinear S.asCharges (by
    simp only [accSU2, toSpecies_apply_asCharges, Fin.isValue, sum_SMSpecies_numberCharges_one,
      LinearMap.coe_mk, AddHom.coe_mk]
    simp [asCharges])
    (by
    simp only [accSU3, SMCharges.toSpecies_apply_eq, sum_SMSpecies_numberCharges_one,
      LinearMap.coe_mk, AddHom.coe_mk, speciesVal, asCharges, neg_add_rev]
    ring)
