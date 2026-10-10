import AFTD.Prelude
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpLineEqProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInCubeProp
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpToSolNS
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableLineEqProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableInQuadProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableInCubeProp
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadCubeToSol
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadCube
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuad
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInLineEq
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInQuadToSol
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInLineEqToSol
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
# MSSMACC.AnomalyFreePerp.toSol

Topic: quantum_field_theory   Node: b3586765966f

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.AnomalyFreePerp.toSol`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/ToSols.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A solution from an element of `MSSMACC.AnomalyFreePerp × ℚ × ℚ × ℚ`. We will show that this map is a surjection.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
/-- A solution from an element of `MSSMACC.AnomalyFreePerp × ℚ × ℚ × ℚ`. We will show that this map is a surjection. -/
def MSSMACC.AnomalyFreePerp.toSol : MSSMACC.AnomalyFreePerp × ℚ × ℚ × ℚ → MSSMACC.Sols := fun (R, a, b, c) =>
  if h₃ : LineEqProp R ∧ InQuadProp R ∧ InCubeProp R then
    inQuadCubeToSol (⟨⟨⟨R, h₃.1⟩, h₃.2.1⟩, h₃.2.2⟩, a, b, c)
  else
    if h₂ : LineEqProp R ∧ InQuadProp R then
      inQuadToSol (⟨⟨R, h₂.1⟩, h₂.2⟩, a, b, c)
    else
      if h₁ : LineEqProp R then
        inLineEqToSol (⟨R, h₁⟩, a, b, c)
      else
        toSolNS ⟨R, a, b, c⟩
