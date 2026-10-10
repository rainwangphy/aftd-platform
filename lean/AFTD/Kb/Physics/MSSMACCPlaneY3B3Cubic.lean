import AFTD.Prelude
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerp
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.MSSMACCsAccCube
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.MSSMACCPlaneY3B3
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCsCubeTriLin
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACCY3
import AFTD.Kb.Physics.MSSMACCB3
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.MSSMACCPlaneY3B3Val
import AFTD.Kb.Physics.TriLinearSymmToCubic
import AFTD.Kb.Physics.TriLinearSymmToCubicAdd
import AFTD.Kb.Physics.MSSMACCLineY3B3Charges
import AFTD.Kb.Physics.MSSMACCLineY3B3ChargesVal
import AFTD.Kb.Physics.MSSMACCLineY3B3ChargesCubic
import AFTD.Kb.Physics.TriLinearSymmMapSmul3
import AFTD.Kb.Physics.MSSMACCLineY3B3
import AFTD.Kb.Physics.MSSMACCLineY3B3Val
import AFTD.Kb.Physics.MSSMACCLineY3B3DoublePoint
import AFTD.Kb.Physics.HomogeneousCubicMapSmul
import AFTD.Kb.Physics.TriLinearSymmMapSmul1
import AFTD.Kb.Physics.TriLinearSymmMapSmul2
import AFTD.Kb.Physics.TriLinearSymmMapAdd3
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.MSSMACCsAccQuad
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk
import AFTD.Kb.Physics.MSSMACCAnomalyFreeQuadMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk''
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction

/-!
# MSSMACC.planeY₃B₃_cubic

Topic: quantum_field_theory   Node: bb86c6360b4c

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.planeY₃B₃_cubic`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/PlaneWithY3B3.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMACC.planeY₃B₃_cubic
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
lemma MSSMACC.planeY₃B₃_cubic (R : MSSMACC.AnomalyFreePerp) (a b c : ℚ) :
    accCube (planeY₃B₃ R a b c).val = c ^ 2 *
    (3 * a * cubeTriLin R.val R.val Y₃.val
    + 3 * b * cubeTriLin R.val R.val B₃.val + c * cubeTriLin R.val R.val R.val) := by
  rw [planeY₃B₃_val]
  rw [accCube, TriLinearSymm.toCubic_add, ← accCube]
  rw [← lineY₃B₃Charges_val]
  rw [lineY₃B₃Charges_cubic]
  rw [TriLinearSymm.map_smul₃, lineY₃B₃Charges_val, ← lineY₃B₃_val]
  rw [lineY₃B₃_doublePoint]
  rw [lineY₃B₃_val, accCube]
  rw [cubeTriLin.toCubic.map_smul]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂]
  rw [cubeTriLin.map_add₃, cubeTriLin.map_smul₃, cubeTriLin.map_smul₃]
  rw [show (TriLinearSymm.toCubic cubeTriLin) R.val = cubeTriLin R.val R.val R.val by rfl]
  ring
