import AFTD.Prelude
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadCubeSol
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
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLineEqPropSol
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadSolProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInCubeSolProp
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
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLinEqPropSolIffProjLinEqProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadSolPropIffProjInQuadProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInCubeSolPropIffProjInCubeProp
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
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableLineEqProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableInQuadProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableInCubeProp

/-!
# MSSMACC.AnomalyFreePerp.inQuadCubeProj

Topic: quantum_field_theory   Node: d3189a1d22aa

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.AnomalyFreePerp.inQuadCubeProj`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/ToSols.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

On elements of `inQuadCubeSol` a right-inverse to `inQuadCubeToSol`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
/-- On elements of `inQuadCubeSol` a right-inverse to `inQuadCubeToSol`. -/
def MSSMACC.AnomalyFreePerp.inQuadCubeProj (T : InQuadCubeSol) : InQuadCube × ℚ × ℚ × ℚ :=
  (⟨⟨⟨proj T.val.1.1, (linEqPropSol_iff_proj_linEqProp T.val).mp T.prop.1⟩,
    (inQuadSolProp_iff_proj_inQuadProp T.val).mp T.prop.2.1⟩,
    (inCubeSolProp_iff_proj_inCubeProp T.val).mp T.prop.2.2⟩,
  (dot Y₃.val B₃.val)⁻¹ * (dot Y₃.val T.val.val - dot B₃.val T.val.val),
  (dot Y₃.val B₃.val)⁻¹ * (2 * dot B₃.val T.val.val - dot Y₃.val T.val.val),
  (dot Y₃.val B₃.val)⁻¹ * 1)
