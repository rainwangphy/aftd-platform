import AFTD.Prelude
import AFTD.Kb.Physics.SMSMNoGravOneLinearParameters
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.SMACCsAccCube
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersAsCharges
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
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirStarComp
import AFTD.Kb.Physics.SMRHNPlusU1QuadSolAccQuadAlpha1Alpha2Zero

/-!
# SM.SMNoGrav.One.linearParameters.cubic_zero_E'_zero

Topic: quantum_field_theory   Node: 91973cb321de

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.One.linearParameters.cubic_zero_E'_zero`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/One/LinearParameterization.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SM.SMNoGrav.One.linearParameters.cubic_zero_E'_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMCharges in
open SMACCs in
open BigOperators in
lemma SM.SMNoGrav.One.linearParameters.cubic_zero_E'_zero (S : linearParameters) (hc : accCube (S.asCharges) = 0)
    (h : S.E' = 0) : S.Q' = 0 := by
  rw [cubic, h] at hc
  simp only [neg_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hc
  have h1 : -(54 * S.Q' ^ 3) - 18 * S.Q' * S.Y ^ 2 = - 18 * (3 * S.Q' ^ 2 + S.Y ^ 2) * S.Q' := by
    ring
  rw [h1] at hc
  simp only [neg_mul, neg_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at hc
  cases' hc with hc hc
  · have h2 := (add_eq_zero_iff_of_nonneg (by nlinarith) (sq_nonneg S.Y)).mp hc
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff,
      false_or] at h2
    exact h2.1
  · exact hc
