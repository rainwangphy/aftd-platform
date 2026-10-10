import AFTD.Prelude
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadSol
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerp
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpToSol
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLineEqPropSol
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadSolProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInCubeSolProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuad
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadProj
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLineEqProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInLineEq
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInCubeProp
import AFTD.Kb.Physics.MSSMACCProj
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInCubeSolPropIffProjInCubeProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadSolPropIffProjInQuadProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLinEqPropSolIffProjLinEqProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadCubeToSol
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadCube
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadToSol
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInLineEqToSol
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpToSolNS
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableLineEqProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableInQuadProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableInCubeProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadToSolProj
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
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction

/-!
# MSSMACC.AnomalyFreePerp.toSol_inQuad

Topic: quantum_field_theory   Node: f8799d8d9cb4

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.AnomalyFreePerp.toSol_inQuad`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/ToSols.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMACC.AnomalyFreePerp.toSol_inQuad
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
lemma MSSMACC.AnomalyFreePerp.toSol_inQuad (T : InQuadSol) : ∃ X, toSol X = T.val := by
  let X := inQuadProj T
  use ⟨X.1.val.val, X.2.1, X.2.2⟩
  have : ¬ InCubeProp X.1.val.val := (inCubeSolProp_iff_proj_inCubeProp T.val).mpr.mt T.prop.2.2
  have : InQuadProp X.1.val.val := (inQuadSolProp_iff_proj_inQuadProp T.val).mp T.prop.2.1
  have : LineEqProp X.1.val.val := (linEqPropSol_iff_proj_linEqProp T.val).mp T.prop.1
  simp_all only [toSol]
  exact inQuadToSol_proj T
