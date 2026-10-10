import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.SMSMNoGrav
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMChargesQ
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.SMACCsAccGrav
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMChargesU
import AFTD.Kb.Physics.SMChargesD
import AFTD.Kb.Physics.SMChargesL
import AFTD.Kb.Physics.SMChargesE
import AFTD.Kb.Physics.SMSMNoGravOneEZeroIffQZero
import AFTD.Kb.Physics.SMChargesToSpeciesEquiv
import AFTD.Kb.Physics.SMChargesSumSMSpeciesNumberChargesOne
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.SMChargesToSpecies
import AFTD.Kb.Physics.SMChargesToSpeciesApplyEq
import AFTD.Kb.Physics.SMACCsAccSU2
import AFTD.Kb.Physics.SMSMNoGravSU2Sol
import AFTD.Kb.Physics.SMACCsAccSU3
import AFTD.Kb.Physics.SMSMNoGravSU3Sol
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
# SM.SMNoGrav.One.accGrav_Q_zero

Topic: quantum_field_theory   Node: 6d0553e6c0d7

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.One.accGrav_Q_zero`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/One/Lemmas.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a set of 1-family SM charges satisfying all ACCs except the gravitational, if the `Q` charge is zero then the charges satisfy the gravitational ACCs.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMCharges in
open SMACCs in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
/-- For a set of 1-family SM charges satisfying all ACCs except the gravitational, if the `Q` charge is zero then the charges satisfy the gravitational ACCs. -/
lemma SM.SMNoGrav.One.accGrav_Q_zero {S : (SMNoGrav 1).Sols} (hQ : Q S.val (0 : Fin 1) = 0) :
    accGrav S.val = 0 := by
  rw [accGrav]
  have hE := E_zero_iff_Q_zero.mp hQ
  simp_all only [toSpecies_apply_eq, Fin.isValue, sum_SMSpecies_numberCharges_one, LinearMap.coe_mk,
    AddHom.coe_mk]
  have h1 := SU2Sol S.1.1
  have h2 := SU3Sol S.1.1
  simp only [accSU2, toSpecies_apply_eq, Fin.isValue, sum_SMSpecies_numberCharges_one,
    LinearMap.coe_mk, AddHom.coe_mk, accSU3] at h1 h2
  erw [hQ] at h1 h2 ⊢
  erw [hE]
  linear_combination 2 * h1 + 3 * h2
