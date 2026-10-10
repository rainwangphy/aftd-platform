import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.SMRHNPlusU1
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.SMRHNPlusU1QuadToAF
import AFTD.Kb.Physics.SMRHNPlusU1LinearToQuad
import AFTD.Kb.Physics.SMRHNRepCharges
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.ACCSystemGroupActionInstGroupGroup
import AFTD.Kb.Physics.ACCSystemGroupActionQuadSolAction
import AFTD.Kb.Physics.ACCSystemGroupActionSolAction

/-!
# SMRHN.PlusU1.linearToAF

Topic: quantum_field_theory   Node: b8a667672d9e

Provenance: formalization of a published result. Source: Physlib, `SMRHN.PlusU1.linearToAF`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/PlusU1/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An element of `LinSols` which satisfies the quadratic and cubic ACCs gives us a element of `Sols`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMRHN SMRHN.PlusU1 in
open SMνCharges in
open SMνACCs in
open BigOperators in
variable {n : ℕ} in
/-- An element of `LinSols` which satisfies the quadratic and cubic ACCs gives us a element of `Sols`. -/
def SMRHN.PlusU1.linearToAF (S : (PlusU1 n).LinSols) (hQ : accQuad S.val = 0)
    (hc : accCube S.val = 0) : (PlusU1 n).Sols :=
  quadToAF (linearToQuad S hQ) hc
