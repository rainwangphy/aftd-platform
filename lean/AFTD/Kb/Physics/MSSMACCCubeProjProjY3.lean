import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCsCubeTriLin
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerp
import AFTD.Kb.Physics.MSSMACCProj
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACCY3
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCDot
import AFTD.Kb.Physics.MSSMACCB3
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.MSSMACCProjVal
import AFTD.Kb.Physics.TriLinearSymmMapAdd1
import AFTD.Kb.Physics.TriLinearSymmMapAdd2
import AFTD.Kb.Physics.MSSMACCLineY3B3
import AFTD.Kb.Physics.MSSMACCLineY3B3DoublePoint
import AFTD.Kb.Physics.TriLinearSymmSwap2
import AFTD.Kb.Physics.TriLinearSymmMapSmul1
import AFTD.Kb.Physics.TriLinearSymmMapSmul3
import AFTD.Kb.Physics.MSSMACCDoublePointY3Y3
import AFTD.Kb.Physics.TriLinearSymmSwap1
import AFTD.Kb.Physics.MSSMACCDoublePointY3B3
import AFTD.Kb.Physics.TriLinearSymmMapSmul2
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
import AFTD.Kb.Physics.ACCSystemSolsMulAction

/-!
# MSSMACC.cube_proj_proj_Y₃

Topic: quantum_field_theory   Node: 4776fdd04d09

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.cube_proj_proj_Y₃`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMACC.cube_proj_proj_Y₃
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
lemma MSSMACC.cube_proj_proj_Y₃ (T : MSSMACC.LinSols) :
    cubeTriLin (proj T).val (proj T).val Y₃.val =
    (dot Y₃.val B₃.val)^2 * cubeTriLin T.val T.val Y₃.val := by
  rw [proj_val]
  rw [cubeTriLin.map_add₁, cubeTriLin.map_add₂]
  conv_lhs =>
    enter [1, 1]
    change ((cubeTriLin (lineY₃B₃ _ _).val) (lineY₃B₃ _ _).val) _
    rw [lineY₃B₃_doublePoint]
  rw [cubeTriLin.map_add₂]
  rw [cubeTriLin.swap₂]
  rw [cubeTriLin.map_add₁, cubeTriLin.map_smul₁, cubeTriLin.map_smul₃]
  rw [doublePoint_Y₃_Y₃]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₃, cubeTriLin.swap₁]
  rw [doublePoint_Y₃_B₃]
  rw [cubeTriLin.map_add₂]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂]
  rw [cubeTriLin.swap₁, cubeTriLin.swap₂]
  rw [doublePoint_Y₃_Y₃]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂]
  rw [cubeTriLin.swap₁, cubeTriLin.swap₂, cubeTriLin.swap₁]
  rw [doublePoint_Y₃_B₃]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂]
  ring
