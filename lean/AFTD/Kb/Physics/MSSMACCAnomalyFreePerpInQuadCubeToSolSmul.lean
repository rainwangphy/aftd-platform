import AFTD.Prelude
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadCube
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadCubeToSol
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsExt
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.MSSMACCPlaneY3B3
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLineEqProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInLineEq
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuad
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInCubeProp
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.MSSMACCPlaneY3B3Smul
import AFTD.Kb.Physics.MSSMCharges
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
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableLineEqProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableInQuadProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableInCubeProp

/-!
# MSSMACC.AnomalyFreePerp.inQuadCubeToSol_smul

Topic: quantum_field_theory   Node: 239f9e966ced

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.AnomalyFreePerp.inQuadCubeToSol_smul`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/ToSols.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMACC.AnomalyFreePerp.inQuadCubeToSol_smul
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
lemma MSSMACC.AnomalyFreePerp.inQuadCubeToSol_smul (R : InQuadCube) (c₁ c₂ c₃ d : ℚ) :
    inQuadCubeToSol (R, (d * c₁), (d * c₂), (d * c₃)) = d • inQuadCubeToSol (R, c₁, c₂, c₃) := by
  apply ACCSystem.Sols.ext
  change (planeY₃B₃ _ _ _ _).val = _
  rw [planeY₃B₃_smul]
  rfl
