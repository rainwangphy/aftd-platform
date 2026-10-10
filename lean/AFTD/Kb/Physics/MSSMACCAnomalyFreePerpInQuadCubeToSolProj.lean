import AFTD.Prelude
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadCubeSol
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadCubeToSol
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadCubeProj
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLineEqPropSol
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadSolProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInCubeSolProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadCube
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuad
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInCubeProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLineEqProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInLineEq
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadProp
import AFTD.Kb.Physics.MSSMACCProj
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCDot
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.MSSMACCY3
import AFTD.Kb.Physics.MSSMACCB3
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadCubeToSolSmul
import AFTD.Kb.Physics.ACCSystemSolsExt
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.MSSMACCPlaneY3B3
import AFTD.Kb.Physics.MSSMACCPlaneY3B3Val
import AFTD.Kb.Physics.MSSMACCY3PlusB3PlusProj
import AFTD.Kb.Physics.ACCSystemCharges
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
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableLineEqProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableInQuadProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableInCubeProp

/-!
# MSSMACC.AnomalyFreePerp.inQuadCubeToSol_proj

Topic: quantum_field_theory   Node: 9efe4ef7cf95

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.AnomalyFreePerp.inQuadCubeToSol_proj`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/ToSols.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMACC.AnomalyFreePerp.inQuadCubeToSol_proj
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
lemma MSSMACC.AnomalyFreePerp.inQuadCubeToSol_proj (T : InQuadCubeSol) :
    inQuadCubeToSol (inQuadCubeProj T) = T.val := by
  rw [inQuadCubeProj, inQuadCubeToSol_smul]
  apply ACCSystem.Sols.ext
  change _ • (planeY₃B₃ _ _ _ _).val = _
  rw [planeY₃B₃_val, Y₃_plus_B₃_plus_proj]
  ring_nf
  simp only [zero_smul, add_zero, zero_add]
  rw [← SemigroupAction.mul_smul, mul_comm, mul_inv_cancel₀]
  · exact MulAction.one_smul (T.1).val
  · rw [show dot Y₃.val B₃.val = 108 by with_unfolding_all rfl]
    exact Ne.symm (OfNat.zero_ne_ofNat 108)
