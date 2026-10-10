import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.SMRHNPlusU1
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.SMRHNPlusU1QuadSolToSolAlpha1
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
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.ACCSystemGroupActionInstGroupGroup
import AFTD.Kb.Physics.ACCSystemGroupActionQuadSolAction
import AFTD.Kb.Physics.ACCSystemGroupActionSolAction

/-!
# SMRHN.PlusU1.quadSolToSolInv

Topic: quantum_field_theory   Node: c173114e2ee3

Provenance: formalization of a published result. Source: Physlib, `SMRHN.PlusU1.quadSolToSolInv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/PlusU1/QuadSolToSol.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A map from `Sols` to `QuadSols × ℚ × ℚ` which forms a right-inverse to `quadSolToSol`, as shown in `quadSolToSolInv_rightInverse`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMRHN.PlusU1.QuadSolToSol in
/-- A map from `Sols` to `QuadSols × ℚ × ℚ` which forms a right-inverse to `quadSolToSol`, as shown in `quadSolToSolInv_rightInverse`. -/
def SMRHN.PlusU1.quadSolToSolInv {n : ℕ} : (PlusU1 n).Sols → (PlusU1 n).QuadSols × ℚ × ℚ :=
    fun S =>
  if α₁ S.1 = 0 then
    (S.1, 1, 0)
  else
    (S.1, (α₁ S.1)⁻¹, 0)
