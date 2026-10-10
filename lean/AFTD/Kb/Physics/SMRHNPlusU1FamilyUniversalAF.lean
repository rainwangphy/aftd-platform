import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.SMRHNPlusU1
import AFTD.Kb.Physics.SMRHNPlusU1ChargeToAF
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMRHNFamilyUniversal
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.SMRHNFamilyUniversalAccCube
import AFTD.Kb.Physics.SMRHNPlusU1CubeSol
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMRHNFamilyUniversalAccQuad
import AFTD.Kb.Physics.SMRHNPlusU1QuadSol
import AFTD.Kb.Physics.SMNuACCsAccGrav
import AFTD.Kb.Physics.SMRHNFamilyUniversalAccGrav
import AFTD.Kb.Physics.SMRHNPlusU1GravSol
import AFTD.Kb.Physics.SMNuACCsAccSU2
import AFTD.Kb.Physics.SMRHNFamilyUniversalAccSU2
import AFTD.Kb.Physics.SMRHNPlusU1SU2Sol
import AFTD.Kb.Physics.SMNuACCsAccSU3
import AFTD.Kb.Physics.SMRHNFamilyUniversalAccSU3
import AFTD.Kb.Physics.SMRHNPlusU1SU3Sol
import AFTD.Kb.Physics.SMNuACCsAccYY
import AFTD.Kb.Physics.SMRHNFamilyUniversalAccYY
import AFTD.Kb.Physics.SMRHNPlusU1YYsol
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
# SMRHN.PlusU1.familyUniversalAF

Topic: quantum_field_theory   Node: 745e514d9b27

Provenance: formalization of a published result. Source: Physlib, `SMRHN.PlusU1.familyUniversalAF`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/PlusU1/FamilyMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The family universal maps on `Sols`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMRHN SMRHN.PlusU1 in
open SMνCharges in
open SMνACCs in
open BigOperators in
variable {n : ℕ} in
set_option backward.isDefEq.respectTransparency false in
/-- The family universal maps on `Sols`. -/
def SMRHN.PlusU1.familyUniversalAF (n : ℕ) :
    (PlusU1 1).Sols → (PlusU1 n).Sols := fun S =>
  chargeToAF (familyUniversal n S.val)
    (by rw [familyUniversal_accGrav, gravSol S.1.1, mul_zero])
    (by rw [familyUniversal_accSU2, SU2Sol S.1.1, mul_zero])
    (by rw [familyUniversal_accSU3, SU3Sol S.1.1, mul_zero])
    (by rw [familyUniversal_accYY, YYsol S.1.1, mul_zero])
    (by rw [familyUniversal_accQuad, quadSol S.1, mul_zero])
    (by rw [familyUniversal_accCube, cubeSol S, mul_zero])
