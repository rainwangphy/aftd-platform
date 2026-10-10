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
import AFTD.Kb.Physics.SMChargesE
import AFTD.Kb.Physics.SMSMNoGravOneEZeroIffQZero
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersQENeqZero
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersQENeqZeroBijection
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.SMACCsAccCube
import AFTD.Kb.Physics.SMSMNoGravCubeSol
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersQENeqZeroGravOfCubic
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
# SM.SMNoGrav.One.accGrav_Q_ne_zero

Topic: quantum_field_theory   Node: 3e7167f24ec7

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.One.accGrav_Q_ne_zero`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/One/Lemmas.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a set of 1-family SM charges satisfying all ACCs except the gravitational, if the `Q` charge is not zero then the charges satisfy the gravitational ACCs.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMCharges in
open SMACCs in
open BigOperators in
/-- For a set of 1-family SM charges satisfying all ACCs except the gravitational, if the `Q` charge is not zero then the charges satisfy the gravitational ACCs. -/
lemma SM.SMNoGrav.One.accGrav_Q_ne_zero {S : (SMNoGrav 1).Sols} (hQ : Q S.val (0 : Fin 1) ≠ 0) :
    accGrav S.val = 0 := by
  have hE := E_zero_iff_Q_zero.mpr.mt hQ
  let S' := linearParametersQENeqZero.bijection.symm ⟨S.1.1, hQ, hE⟩
  have hC := cubeSol S
  have hS' := congrArg (fun S => S.val.val)
    (linearParametersQENeqZero.bijection.right_inv ⟨S.1.1, hQ, hE⟩)
  change _ = S.val at hS'
  rw [← hS'] at hC ⊢
  exact S'.grav_of_cubic hC
