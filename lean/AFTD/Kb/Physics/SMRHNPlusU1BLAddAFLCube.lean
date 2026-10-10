import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.SMRHNPlusU1
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.SMRHNPlusU1BL
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.SMNuACCsCubeTriLin
import AFTD.Kb.Physics.TriLinearSymmToCubic
import AFTD.Kb.Physics.TriLinearSymmToCubicAdd
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.SMRHNPlusU1CubeSol
import AFTD.Kb.Physics.HomogeneousCubicMapSmul
import AFTD.Kb.Physics.TriLinearSymmMapSmul1
import AFTD.Kb.Physics.TriLinearSymmMapSmul2
import AFTD.Kb.Physics.TriLinearSymmMapSmul3
import AFTD.Kb.Physics.SMRHNPlusU1BLOnCubeTriLinAFL
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.SMRHNFamilyUniversal
import AFTD.Kb.Physics.SMRHNPlusU1BL1
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMRHNRepCharges
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemGroupActionInstGroupGroup
import AFTD.Kb.Physics.ACCSystemGroupActionQuadSolAction
import AFTD.Kb.Physics.ACCSystemGroupActionSolAction

/-!
# SMRHN.PlusU1.BL.add_AFL_cube

Topic: quantum_field_theory   Node: b8a3631e2db4

Provenance: formalization of a published result. Source: Physlib, `SMRHN.PlusU1.BL.add_AFL_cube`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/PlusU1/BMinusL.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMRHN.PlusU1.BL.add_AFL_cube
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMRHN SMRHN.PlusU1 SMRHN.PlusU1.BL in
open SMνCharges in
open SMνACCs in
open BigOperators in
variable {n : ℕ} in
variable {n : ℕ} in
set_option backward.isDefEq.respectTransparency false in
lemma SMRHN.PlusU1.BL.add_AFL_cube (S : (PlusU1 n).LinSols) (a b : ℚ) :
    accCube (a • S.val + b • (BL n).val) =
    a ^ 2 * (a * accCube S.val + 3 * b * cubeTriLin S.val S.val (BL n).val) := by
  erw [TriLinearSymm.toCubic_add, cubeSol (b • (BL n)), accCube.map_smul]
  repeat rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂, cubeTriLin.map_smul₃]
  rw [on_cubeTriLin_AFL]
  simp only [HomogeneousCubic, accCube, TriLinearSymm.toCubic_apply,
    add_zero, BL_val, mul_zero]
  ring
