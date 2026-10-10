import AFTD.Prelude
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersQENeqZero
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.SMACCsAccCube
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.SMSMNoGrav
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.SMChargesQ
import AFTD.Kb.Physics.SMChargesE
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersQENeqZeroBijection
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersAsCharges
import AFTD.Kb.Physics.SMSMNoGravOneLinearParameters
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersQENeqZeroBijectionLinearParameters
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersQENeqZeroBijectionCoeVal
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersCubic
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.SMACCsAccQuad
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction

/-!
# SM.SMNoGrav.One.linearParametersQENeqZero.cubic

Topic: quantum_field_theory   Node: 8a38630a5258

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.One.linearParametersQENeqZero.cubic`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/One/LinearParameterization.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SM.SMNoGrav.One.linearParametersQENeqZero.cubic
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMCharges in
open SMACCs in
open BigOperators in
lemma SM.SMNoGrav.One.linearParametersQENeqZero.cubic (S : linearParametersQENeqZero) :
    accCube (bijection S).1.val = 0 ↔ S.v ^ 3 + S.w ^ 3 = -1 := by
  rw [bijection_coe_val, linearParameters.cubic]
  simp only [ne_eq, bijectionLinearParameters_apply_coe_Q', neg_mul,
    bijectionLinearParameters_apply_coe_Y, div_pow, bijectionLinearParameters_apply_coe_E']
  have hvw := S.hvw
  have hQ := S.hx
  field_simp
  simp [hQ]
  ring_nf
  have h1 : -216 - S.v ^ 3 * 216 - S.w ^ 3 * 216 = - 216 *(S.v ^3 + S.w ^3 +1) := by
    ring
  rw [h1]
  simp_all
  exact add_eq_zero_iff_eq_neg
