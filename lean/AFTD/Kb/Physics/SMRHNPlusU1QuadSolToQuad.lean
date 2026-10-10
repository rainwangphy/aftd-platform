import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.SMRHNPlusU1
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.SMRHNPlusU1QuadSolAlpha1
import AFTD.Kb.Physics.SMRHNPlusU1QuadSolAlpha2
import AFTD.Kb.Physics.SMRHNPlusU1QuadSolSpecialToQuad
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.SMRHNPlusU1QuadSolGenericToQuad
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.SMRHNRepCharges
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
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.ACCSystemGroupActionInstGroupGroup
import AFTD.Kb.Physics.ACCSystemGroupActionQuadSolAction
import AFTD.Kb.Physics.ACCSystemGroupActionSolAction
import AFTD.Kb.Physics.SMRHNSM

/-!
# SMRHN.PlusU1.QuadSol.toQuad

Topic: quantum_field_theory   Node: 1a7e9d092a42

Provenance: formalization of a published result. Source: Physlib, `SMRHN.PlusU1.QuadSol.toQuad`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/PlusU1/QuadSol.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The construction of a `QuadSols` from a `LinSols` and two rationals taking account of the generic and special cases. This function is a surjection.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMRHN SMRHN.PlusU1 SMRHN.PlusU1.QuadSol in
open SMνCharges in
open SMνACCs in
open BigOperators in
variable {n : ℕ} in
variable (C : (PlusU1 n).QuadSols) in
/-- The construction of a `QuadSols` from a `LinSols` and two rationals taking account of the generic and special cases. This function is a surjection. -/
def SMRHN.PlusU1.QuadSol.toQuad : (PlusU1 n).LinSols × ℚ × ℚ → (PlusU1 n).QuadSols := fun S =>
  if h : α₁ C S.1 = 0 ∧ α₂ S.1 = 0 then
    specialToQuad C S.1 S.2.1 S.2.2 h.1 h.2
  else
    S.2.1 • genericToQuad C S.1
