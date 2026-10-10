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

/-!
# SM.SMNoGrav.One.linearParametersQENeqZero.cubic_v_zero

Topic: quantum_field_theory   Node: baef22f4c729

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.One.linearParametersQENeqZero.cubic_v_zero`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/One/LinearParameterization.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SM.SMNoGrav.One.linearParametersQENeqZero.cubic_v_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMCharges in
open SMACCs in
open BigOperators in
lemma SM.SMNoGrav.One.linearParametersQENeqZero.cubic_v_zero (S : linearParametersQENeqZero) (h : accCube (bijection S).1.val = 0)
    (hv : S.v = 0) : S.w = -1 := by
  rw [S.cubic, hv] at h
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at h
  have h' : (S.w + 1) * (1 * S.w * S.w + (-1) * S.w + 1) = 0 := by
    ring_nf
    exact add_eq_zero_iff_neg_eq.mpr (id (Eq.symm h))
  have h'' : (1 * (S.w * S.w) + (-1) * S.w + 1) ≠ 0 := by
    refine quadratic_ne_zero_of_discrim_ne_sq ?_ S.w
    intro s
    by_contra hn
    have h : s ^ 2 < 0 := by
      rw [← hn]
      with_unfolding_all rfl
    nlinarith
  simp_all
  exact eq_neg_of_add_eq_zero_left h'
