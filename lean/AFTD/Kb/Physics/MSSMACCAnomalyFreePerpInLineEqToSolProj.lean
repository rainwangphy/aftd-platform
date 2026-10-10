import AFTD.Prelude
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInLineEqSol
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInLineEqToSol
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInLineEqProj
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLineEqPropSol
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadSolProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInLineEq
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLineEqProp
import AFTD.Kb.Physics.MSSMACCProj
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpQuadCoeff
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCsQuadBiLin
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.MSSMACCB3
import AFTD.Kb.Physics.MSSMACCY3
import AFTD.Kb.Physics.MSSMACCDot
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInLineEqToSmul
import AFTD.Kb.Physics.ACCSystemSolsExt
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.MSSMACCLineQuad
import AFTD.Kb.Physics.MSSMACCPlaneY3B3
import AFTD.Kb.Physics.MSSMACCLineQuadVal
import AFTD.Kb.Physics.MSSMACCPlaneY3B3Val
import AFTD.Kb.Physics.MSSMACCY3PlusB3PlusProj
import AFTD.Kb.Physics.MSSMACCQuadProj
import AFTD.Kb.Physics.MSSMACCQuadY3Proj
import AFTD.Kb.Physics.MSSMACCQuadB3Proj
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadSolPropIffQuadCoeffZero
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
# MSSMACC.AnomalyFreePerp.inLineEqToSol_proj

Topic: quantum_field_theory   Node: be25b37cdec4

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.AnomalyFreePerp.inLineEqToSol_proj`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/ToSols.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMACC.AnomalyFreePerp.inLineEqToSol_proj
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
lemma MSSMACC.AnomalyFreePerp.inLineEqToSol_proj (T : InLineEqSol) : inLineEqToSol (inLineEqProj T) = T.val := by
  rw [inLineEqProj, inLineEqTo_smul]
  apply ACCSystem.Sols.ext
  change _ • (lineQuad _ _ _ _).val = _
  rw [lineQuad_val]
  rw [planeY₃B₃_val]
  rw [Y₃_plus_B₃_plus_proj]
  rw [quad_proj, quad_Y₃_proj, quad_B₃_proj]
  ring_nf
  simp only [zero_smul, add_zero, zero_add]
  have h1 : (quadBiLin Y₃.val T.val.val ^ 2 * dot Y₃.val B₃.val ^ 2 * 2 +
      dot Y₃.val B₃.val ^ 2 * quadBiLin B₃.val T.val.val ^ 2 * 2) = quadCoeff T.val := by
    rw [quadCoeff]
    ring
  rw [h1]
  have h2 := (inQuadSolProp_iff_quadCoeff_zero T.val).mpr.mt T.prop.2
  rw [← SemigroupAction.mul_smul, mul_comm, mul_inv_cancel₀ h2]
  exact MulAction.one_smul T.1.val
