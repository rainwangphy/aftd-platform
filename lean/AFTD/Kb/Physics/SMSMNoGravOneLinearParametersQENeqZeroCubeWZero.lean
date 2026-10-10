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
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersQENeqZeroToLinearParameters
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
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirStarComp
import AFTD.Kb.Physics.SMRHNPlusU1QuadSolAccQuadAlpha1Alpha2Zero

/-!
# SM.SMNoGrav.One.linearParametersQENeqZero.cube_w_zero

Topic: quantum_field_theory   Node: 1b918aaaef11

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.One.linearParametersQENeqZero.cube_w_zero`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/One/LinearParameterization.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SM.SMNoGrav.One.linearParametersQENeqZero.cube_w_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMCharges in
open SMACCs in
open BigOperators in
lemma SM.SMNoGrav.One.linearParametersQENeqZero.cube_w_zero (S : linearParametersQENeqZero) (h : accCube (bijection S).1.val = 0)
    (hw : S.w = 0) : S.v = -1 := by
  rw [S.cubic, hw] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h
  have h' : (S.v + 1) * (1 * S.v * S.v + (-1) * S.v + 1) = 0 := by
    ring_nf
    exact add_eq_zero_iff_neg_eq.mpr (id (Eq.symm h))
  have h'' : (1 * (S.v * S.v) + (-1) * S.v + 1) ≠ 0 := by
    refine quadratic_ne_zero_of_discrim_ne_sq ?_ S.v
    intro s
    by_contra hn
    have h : s ^ 2 < 0 := by
      rw [← hn]
      with_unfolding_all rfl
    nlinarith
  simp_all only [one_mul, neg_mul, mul_eq_zero, ne_eq, or_false]
  exact eq_neg_of_add_eq_zero_left h'
