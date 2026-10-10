import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInCubeSolProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpCubicCoeff
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCDot
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.MSSMACCY3
import AFTD.Kb.Physics.MSSMACCB3
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLineEqPropSol
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCsCubeTriLin
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.MSSMACCsAccQuad
import AFTD.Kb.Physics.MSSMACCsAccCube
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk
import AFTD.Kb.Physics.MSSMACCAnomalyFreeQuadMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk''
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.SMSMNoGravOneLinearParametersCubicZeroE'Zero
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirStarComp
import AFTD.Kb.Physics.SMRHNPlusU1QuadSolAccQuadAlpha1Alpha2Zero

/-!
# MSSMACC.AnomalyFreePerp.inCubeSolProp_iff_cubicCoeff_zero

Topic: quantum_field_theory   Node: c83831c189fd

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.AnomalyFreePerp.inCubeSolProp_iff_cubicCoeff_zero`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/ToSols.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMACC.AnomalyFreePerp.inCubeSolProp_iff_cubicCoeff_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
lemma MSSMACC.AnomalyFreePerp.inCubeSolProp_iff_cubicCoeff_zero (T : MSSMACC.Sols) :
    InCubeSolProp T ↔ cubicCoeff T = 0 := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · rw [cubicCoeff, h.1, h.2]
    with_unfolding_all rfl
  · rw [cubicCoeff, show dot Y₃.val B₃.val = 108 by with_unfolding_all rfl] at h
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, ne_eq,
      not_false_eq_true, pow_eq_zero_iff, or_self, false_or] at h
    apply (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp at h
    simp only [ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff] at h
    exact h.symm
