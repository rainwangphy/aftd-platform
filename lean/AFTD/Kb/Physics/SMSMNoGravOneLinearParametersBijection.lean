import AFTD.Prelude
import AFTD.Kb.Physics.SMSMNoGravOneLinearParameters
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.SMSMNoGrav
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMChargesQ
import AFTD.Kb.Physics.SMChargesU
import AFTD.Kb.Physics.SMChargesD
import AFTD.Kb.Physics.SMChargesE
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersAsLinear
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersExt
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersAsCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersAsLinearVal
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMChargesToSpeciesEquiv
import AFTD.Kb.Physics.SMChargesToSpecies
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersSpeciesVal
import AFTD.Kb.Physics.SMChargesToSpeciesApplyEq
import AFTD.Kb.Physics.ACCSystemLinearLinSolsExt
import AFTD.Kb.Physics.SMChargesChargesEqToSpeciesEq
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersToSpeciesApplyAsCharges
import AFTD.Kb.Physics.SMACCsAccSU3
import AFTD.Kb.Physics.SMSMNoGravSU3Sol
import AFTD.Kb.Physics.SMACCsAccSU2
import AFTD.Kb.Physics.SMSMNoGravSU2Sol
import AFTD.Kb.Physics.SMChargesSumSMSpeciesNumberChargesOne
import AFTD.Kb.Physics.SMChargesL
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
# SM.SMNoGrav.One.linearParameters.bijection

Topic: quantum_field_theory   Node: e0612d2cca20

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.One.linearParameters.bijection`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/One/LinearParameterization.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The bijection between the type of linear parameters and `(SMNoGrav 1).LinSols`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMCharges in
open SMACCs in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
/-- The bijection between the type of linear parameters and `(SMNoGrav 1).LinSols`. -/
def SM.SMNoGrav.One.linearParameters.bijection : linearParameters ≃ (SMNoGrav 1).LinSols where
  toFun S := S.asLinear
  invFun S := ⟨SMCharges.Q S.val (0 : Fin 1), (SMCharges.U S.val (0 : Fin 1) -
      SMCharges.D S.val (0 : Fin 1))/2,
      SMCharges.E S.val (0 : Fin 1)⟩
  left_inv S := by
    apply linearParameters.ext
    · rfl
    · simp only [Fin.isValue]
      repeat erw [asLinear_val]
      simp only [Fin.isValue, toSpecies_apply]
      repeat erw [speciesVal]
      simp only [asCharges, neg_add_rev]
      ring
    · rfl
  right_inv S := by
    simp only [Fin.isValue, toSpecies_apply_eq]
    apply ACCSystemLinear.LinSols.ext
    rw [charges_eq_toSpecies_eq]
    intro i
    rw [asLinear_val]
    funext j
    have hj : j = (0 : Fin 1) := by
      match j with
      | ⟨0, _⟩ => rfl
    subst hj
    rw [toSpecies_apply_asCharges]
    have h1 := SU3Sol S
    simp only [accSU3, toSpecies_apply_eq, Fin.isValue, sum_SMSpecies_numberCharges_one,
      LinearMap.coe_mk, AddHom.coe_mk] at h1
    have h2 := SU2Sol S
    simp only [accSU2,
      Fin.isValue, toSpecies_apply_eq, sum_SMSpecies_numberCharges_one,
      LinearMap.coe_mk, AddHom.coe_mk] at h2
    match i with
    | 0 => rfl
    | 1 =>
      simp only [asCharges, Fin.isValue, toSpecies_apply_eq]
      field_simp
      linear_combination (norm := ring_nf) -(1 * h1)
      simp only [Fin.isValue, Fin.zero_eta, toSpeciesEquiv_apply, Nat.reduceMul]
      ring
    | 2 =>
      simp only [asCharges, Fin.isValue, neg_add_rev, toSpecies_apply_eq]
      field_simp
      linear_combination (norm := ring_nf) -(1 * h1)
      simp only [Fin.isValue, Fin.zero_eta, toSpeciesEquiv_apply, Nat.reduceMul]
      ring
    | 3 =>
      simp only [asCharges, Fin.isValue, neg_mul, toSpecies_apply_eq]
      field_simp
      linear_combination (norm := ring_nf) -(1 * h2)
      simp only [Fin.isValue, Fin.zero_eta, toSpeciesEquiv_apply, Nat.reduceMul]
      ring
    | 4 => rfl
