import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACC
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
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerp
import AFTD.Kb.Physics.MSSMACCProj
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCDot
import AFTD.Kb.Physics.MSSMACCY3
import AFTD.Kb.Physics.MSSMACCB3
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.MSSMACCProjVal
import AFTD.Kb.Physics.TriLinearSymmMapAdd1
import AFTD.Kb.Physics.TriLinearSymmMapAdd2
import AFTD.Kb.Physics.MSSMACCLineY3B3
import AFTD.Kb.Physics.MSSMACCLineY3B3Val
import AFTD.Kb.Physics.MSSMACCLineY3B3DoublePoint
import AFTD.Kb.Physics.TriLinearSymmMapSmul1
import AFTD.Kb.Physics.TriLinearSymmMapSmul2
import AFTD.Kb.Physics.TriLinearSymmToCubic
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.MSSMACCCubicACCApply
import AFTD.Kb.Physics.TriLinearSymmSwap1
import AFTD.Kb.Physics.TriLinearSymmSwap2
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.MSSMACCsAccQuad
import AFTD.Kb.Physics.MSSMACCsAccCube
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk
import AFTD.Kb.Physics.MSSMACCAnomalyFreeQuadMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk''
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction

/-!
# MSSMACC.cube_proj_proj_self

Topic: quantum_field_theory   Node: 9e30198f12af

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.cube_proj_proj_self`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMACC.cube_proj_proj_self
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
lemma MSSMACC.cube_proj_proj_self (T : MSSMACC.Sols) :
    cubeTriLin (proj T.1.1).val (proj T.1.1).val T.val =
    2 * dot Y₃.val B₃.val *
    ((dot B₃.val T.val - dot Y₃.val T.val) * cubeTriLin T.val T.val Y₃.val +
    (dot Y₃.val T.val - 2 * dot B₃.val T.val) * cubeTriLin T.val T.val B₃.val) := by
  rw [proj_val]
  rw [cubeTriLin.map_add₁, cubeTriLin.map_add₂]
  rw [← lineY₃B₃_val, lineY₃B₃_doublePoint, lineY₃B₃_val]
  repeat rw [cubeTriLin.map_add₁]
  repeat rw [cubeTriLin.map_smul₁]
  repeat rw [cubeTriLin.map_add₂]
  repeat rw [cubeTriLin.map_smul₂]
  rw [← cubeTriLin.toCubic_apply]
  rw [← cubicACC_apply]
  rw [T.cubicSol]
  rw [cubeTriLin.swap₁ Y₃.val T.val T.val, cubeTriLin.swap₂ T.val Y₃.val T.val]
  rw [cubeTriLin.swap₁ B₃.val T.val T.val, cubeTriLin.swap₂ T.val B₃.val T.val]
  ring
