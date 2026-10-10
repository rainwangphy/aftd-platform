import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.SMRHNSM
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMNuACCsAccSU2
import AFTD.Kb.Physics.SMRHNFamilyUniversal
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.SMNuACCsAccGrav
import AFTD.Kb.Physics.SMRHNFamilyUniversalAccGrav
import AFTD.Kb.Physics.SMRHNSMGravSol
import AFTD.Kb.Physics.SMNuACCsAccSU3
import AFTD.Kb.Physics.SMRHNFamilyUniversalAccSU3
import AFTD.Kb.Physics.SMRHNSMSU3Sol
import AFTD.Kb.Physics.SMRHNSMChargeToLinear
import AFTD.Kb.Physics.ACCSystemLinearLinSolsExt
import AFTD.Kb.Physics.SMRHNFamilyUniversalAccSU2
import AFTD.Kb.Physics.SMRHNSMSU2Sol
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.SMRHNRepCharges
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.ACCSystemGroupActionInstGroupGroup
import AFTD.Kb.Physics.ACCSystemGroupActionQuadSolAction
import AFTD.Kb.Physics.ACCSystemGroupActionSolAction

/-!
# SMRHN.SM.familyUniversalLinear

Topic: quantum_field_theory   Node: 664730e6e94b

Provenance: formalization of a published result. Source: Physlib, `SMRHN.SM.familyUniversalLinear`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Ordinary/FamilyMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The family universal maps on `LinSols`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMRHN SMRHN.SM in
open SMνCharges in
open SMνACCs in
open BigOperators in
variable {n : ℕ} in
set_option backward.isDefEq.respectTransparency false in
/-- The family universal maps on `LinSols`. -/
def SMRHN.SM.familyUniversalLinear (n : ℕ) :
    (SM 1).LinSols →ₗ[ℚ] (SM n).LinSols where
  toFun S := chargeToLinear (familyUniversal n S.val)
    (by rw [familyUniversal_accGrav, gravSol S, mul_zero])
    (by rw [familyUniversal_accSU2, SU2Sol S, mul_zero])
    (by rw [familyUniversal_accSU3, SU3Sol S, mul_zero])
  map_add' S T := ACCSystemLinear.LinSols.ext ((familyUniversal n).map_add' _ _)
  map_smul' a S := ACCSystemLinear.LinSols.ext ((familyUniversal n).map_smul' _ _)
