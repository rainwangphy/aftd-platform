import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.SMRHNPlusU1
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.SMNuACCsCubeTriLin
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.SMRHNPlusU1BL
import AFTD.Kb.Physics.SMNuACCsAccGrav
import AFTD.Kb.Physics.SMNuACCsAccSU3
import AFTD.Kb.Physics.SMRHNPlusU1BL1
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.SMNuChargesQ
import AFTD.Kb.Physics.SMNuChargesU
import AFTD.Kb.Physics.SMNuChargesD
import AFTD.Kb.Physics.SMNuChargesL
import AFTD.Kb.Physics.SMNuChargesE
import AFTD.Kb.Physics.SMNuChargesN
import AFTD.Kb.Physics.SMRHNFamilyUniversal
import AFTD.Kb.Physics.SMRHNFamilyUniversalCubeTriLin'
import AFTD.Kb.Physics.SMNuACCsAccGravDecomp
import AFTD.Kb.Physics.SMNuACCsAccSU3Decomp
import AFTD.Kb.Physics.SMNuChargesToSpeciesEquiv
import AFTD.Kb.Physics.SMNuChargesToSpecies
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.SMRHNRepCharges
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.HomogeneousCubicInstFun
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
import AFTD.Kb.GameTheoryEconomics.LxvVal

/-!
# SMRHN.PlusU1.BL.on_cubeTriLin

Topic: quantum_field_theory   Node: eb43e9c58af7

Provenance: formalization of a published result. Source: Physlib, `SMRHN.PlusU1.BL.on_cubeTriLin`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/PlusU1/BMinusL.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMRHN.PlusU1.BL.on_cubeTriLin
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMRHN SMRHN.PlusU1 in
open SMνCharges in
open SMνACCs in
open BigOperators in
variable {n : ℕ} in
variable {n : ℕ} in
set_option backward.isDefEq.respectTransparency false in
lemma SMRHN.PlusU1.BL.on_cubeTriLin (S : (PlusU1 n).Charges) :
    cubeTriLin (BL n).val (BL n).val S = 9 * accGrav S - 24 * accSU3 S := by
  erw [familyUniversal_cubeTriLin']
  rw [accGrav_decomp, accSU3_decomp]
  simp only [Fin.isValue, BL₁_val, mul_one, toSpecies_apply, mul_neg,
    neg_neg, neg_mul]
  ring
