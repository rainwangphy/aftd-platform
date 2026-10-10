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
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACCLineY3B3
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.MSSMACCY3
import AFTD.Kb.Physics.MSSMACCB3
import AFTD.Kb.Physics.TriLinearSymmMapAdd2
import AFTD.Kb.Physics.TriLinearSymmMapAdd1
import AFTD.Kb.Physics.TriLinearSymmMapSmul2
import AFTD.Kb.Physics.TriLinearSymmMapSmul1
import AFTD.Kb.Physics.MSSMACCDoublePointY3Y3
import AFTD.Kb.Physics.TriLinearSymmSwap1
import AFTD.Kb.Physics.MSSMACCDoublePointY3B3
import AFTD.Kb.Physics.MSSMACCDoublePointB3B3
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.MSSMACCsAccQuad
import AFTD.Kb.Physics.MSSMACCsAccCube
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk
import AFTD.Kb.Physics.MSSMACCAnomalyFreeQuadMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk''
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction

/-!
# MSSMACC.lineY₃B₃_doublePoint

Topic: quantum_field_theory   Node: 02e65784925a

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.lineY₃B₃_doublePoint`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/LineY3B3.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMACC.lineY₃B₃_doublePoint
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
lemma MSSMACC.lineY₃B₃_doublePoint (R : MSSMACC.LinSols) (a b : ℚ) :
    cubeTriLin (lineY₃B₃ a b).val (lineY₃B₃ a b).val R.val = 0 := by
  change cubeTriLin (a • Y₃.val + b • B₃.val) (a • Y₃.val + b • B₃.val) R.val = 0
  rw [cubeTriLin.map_add₂, cubeTriLin.map_add₁, cubeTriLin.map_add₁]
  repeat rw [cubeTriLin.map_smul₂, cubeTriLin.map_smul₁]
  simp only [cubeTriLin.swap₁ B₃.val Y₃.val R.val, doublePoint_B₃_B₃, doublePoint_Y₃_Y₃,
    doublePoint_Y₃_B₃, mul_zero, add_zero]
