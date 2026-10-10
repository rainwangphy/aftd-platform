import AFTD.Prelude
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadSol
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadToSol
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadProj
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLineEqPropSol
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadSolProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInCubeSolProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuad
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInLineEq
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLineEqProp
import AFTD.Kb.Physics.MSSMACCProj
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpCubicCoeff
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCsCubeTriLin
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.MSSMACCB3
import AFTD.Kb.Physics.MSSMACCY3
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCDot
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadToSolSmul
import AFTD.Kb.Physics.ACCSystemSolsExt
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.MSSMACCPlaneY3B3
import AFTD.Kb.Physics.MSSMACCAlpha1
import AFTD.Kb.Physics.MSSMACCPlaneY3B3Val
import AFTD.Kb.Physics.MSSMACCY3PlusB3PlusProj
import AFTD.Kb.Physics.MSSMACCCubeProj
import AFTD.Kb.Physics.MSSMACCCubeProjProjB3
import AFTD.Kb.Physics.MSSMACCCubeProjProjY3
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInCubeSolPropIffCubicCoeffZero
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
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableLineEqProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableInQuadProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableInCubeProp

/-!
# MSSMACC.AnomalyFreePerp.inQuadToSol_proj

Topic: quantum_field_theory   Node: 4dffb542bd18

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.AnomalyFreePerp.inQuadToSol_proj`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/ToSols.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMACC.AnomalyFreePerp.inQuadToSol_proj
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
lemma MSSMACC.AnomalyFreePerp.inQuadToSol_proj (T : InQuadSol) : inQuadToSol (inQuadProj T) = T.val := by
  rw [inQuadProj, inQuadToSol_smul]
  apply ACCSystem.Sols.ext
  change _ • (planeY₃B₃ _ _ _ _).val = _
  rw [planeY₃B₃_val, Y₃_plus_B₃_plus_proj, cube_proj, cube_proj_proj_B₃, cube_proj_proj_Y₃]
  ring_nf
  simp only [zero_smul, add_zero, zero_add]
  have h1 : (cubeTriLin T.val.val T.val.val Y₃.val ^ 2 * dot Y₃.val B₃.val ^ 3 * 3 +
      dot Y₃.val B₃.val ^ 3 * cubeTriLin T.val.val T.val.val B₃.val ^ 2* 3) = cubicCoeff T.val := by
    rw [cubicCoeff]
    ring
  rw [h1]
  have h2 := (inCubeSolProp_iff_cubicCoeff_zero T.val).mpr.mt T.prop.2.2
  rw [← SemigroupAction.mul_smul, mul_comm, mul_inv_cancel₀ h2]
  exact MulAction.one_smul T.1.val
