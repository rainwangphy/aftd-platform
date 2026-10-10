import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCsQuadBiLin
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACCY3
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerp
import AFTD.Kb.Physics.MSSMACCProj
import AFTD.Kb.Physics.MSSMACCDot
import AFTD.Kb.Physics.MSSMACCB3
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.MSSMACCProjVal
import AFTD.Kb.Physics.BiLinearSymmMapAdd2
import AFTD.Kb.Physics.BiLinearSymmMapSmul2
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
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction

/-!
# MSSMACC.quad_Y₃_proj

Topic: quantum_field_theory   Node: 0dfaab51b1f3

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.quad_Y₃_proj`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMACC.quad_Y₃_proj
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
lemma MSSMACC.quad_Y₃_proj (T : MSSMACC.LinSols) :
    quadBiLin Y₃.val (proj T).val = dot Y₃.val B₃.val * quadBiLin Y₃.val T.val := by
  rw [proj_val]
  rw [quadBiLin.map_add₂, quadBiLin.map_add₂]
  rw [quadBiLin.map_smul₂, quadBiLin.map_smul₂, quadBiLin.map_smul₂]
  rw [show quadBiLin Y₃.val B₃.val = 0 by with_unfolding_all rfl]
  rw [show quadBiLin Y₃.val Y₃.val = 0 by with_unfolding_all rfl]
  ring
