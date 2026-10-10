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
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersQENeqZeroCubic
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
# SM.SMNoGrav.One.linearParametersQENeqZero.cubic_v_or_w_zero

Topic: quantum_field_theory   Node: c40210125d36

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.One.linearParametersQENeqZero.cubic_v_or_w_zero`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/One/LinearParameterization.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SM.SMNoGrav.One.linearParametersQENeqZero.cubic_v_or_w_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMCharges in
open SMACCs in
open BigOperators in
lemma SM.SMNoGrav.One.linearParametersQENeqZero.cubic_v_or_w_zero (S : linearParametersQENeqZero) (h : accCube (bijection S).1.val = 0) :
    S.v = 0 ∨ S.w = 0 := by
  rw [S.cubic] at h
  have h1 : (-1)^3 = (-1 : ℚ) := by rfl
  rw [← h1] at h
  by_contra hn
  rw [not_or] at hn
  have FLTThree := fermatLastTheoremFor_iff_rat.mp fermatLastTheoremThree
  have h2 := FLTThree S.v S.w (-1) hn.1 hn.2 (Ne.symm (ne_of_beq_false (by rfl)))
  exact h2 h
