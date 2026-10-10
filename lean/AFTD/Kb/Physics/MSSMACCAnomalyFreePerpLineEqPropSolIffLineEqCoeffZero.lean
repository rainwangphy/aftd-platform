import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLineEqPropSol
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLineEqCoeff
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCsCubeTriLin
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.MSSMACCY3
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCsQuadBiLin
import AFTD.Kb.Physics.MSSMACCB3
import AFTD.Kb.Physics.MSSMACCDot
import AFTD.Kb.Physics.MSSMACCAlpha3
import AFTD.Kb.Physics.MSSMACCProj
import AFTD.Kb.Physics.MSSMACCAlpha1
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerp
import AFTD.Kb.Physics.MSSMACCCubeProjProjB3
import AFTD.Kb.Physics.MSSMACCCubeProjProjY3
import AFTD.Kb.Physics.MSSMACCQuadB3Proj
import AFTD.Kb.Physics.MSSMACCQuadY3Proj
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
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableLineEqProp
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirStarComp
import AFTD.Kb.Physics.SMRHNPlusU1QuadSolAccQuadAlpha1Alpha2Zero

/-!
# MSSMACC.AnomalyFreePerp.lineEqPropSol_iff_lineEqCoeff_zero

Topic: quantum_field_theory   Node: 5ea3871ad3bb

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.AnomalyFreePerp.lineEqPropSol_iff_lineEqCoeff_zero`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/ToSols.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMACC.AnomalyFreePerp.lineEqPropSol_iff_lineEqCoeff_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
lemma MSSMACC.AnomalyFreePerp.lineEqPropSol_iff_lineEqCoeff_zero (T : MSSMACC.Sols) :
    LineEqPropSol T ↔ lineEqCoeff T = 0 := by
  rw [LineEqPropSol, lineEqCoeff, α₃]
  simp only [mul_eq_zero, OfNat.ofNat_ne_zero,false_or]
  rw [cube_proj_proj_B₃, cube_proj_proj_Y₃, quad_B₃_proj, quad_Y₃_proj]
  rw [show dot Y₃.val B₃.val = 108 by with_unfolding_all rfl]
  simp only [OfNat.ofNat_ne_zero, false_or]
  ring_nf
  rw [mul_comm _ 1259712, mul_comm _ 1259712, ← mul_sub]
  simp
