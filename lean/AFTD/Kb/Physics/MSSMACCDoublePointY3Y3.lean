import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCsCubeTriLin
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACCY3
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.MSSMSpecies
import AFTD.Kb.Physics.MSSMChargesQ
import AFTD.Kb.Physics.MSSMChargesU
import AFTD.Kb.Physics.MSSMChargesD
import AFTD.Kb.Physics.MSSMChargesL
import AFTD.Kb.Physics.MSSMChargesE
import AFTD.Kb.Physics.MSSMChargesN
import AFTD.Kb.Physics.MSSMChargesHd
import AFTD.Kb.Physics.MSSMChargesHu
import AFTD.Kb.Physics.TriLinearSymmMk3
import AFTD.Kb.Physics.MSSMACCsCubeTriLinToFun
import AFTD.Kb.Physics.MSSMACCsCubeTriLinToFunMapSmul1
import AFTD.Kb.Physics.MSSMACCsCubeTriLinToFunMapAdd1
import AFTD.Kb.Physics.MSSMACCsCubeTriLinToFunSwap1
import AFTD.Kb.Physics.MSSMACCsCubeTriLinToFunSwap2
import AFTD.Kb.Physics.MSSMACCY3AsCharge
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.MSSMACCY3Val
import AFTD.Kb.Physics.MSSMChargesToSpecies
import AFTD.Kb.Physics.MSSMChargesToSMSpecies
import AFTD.Kb.Physics.MSSMChargesToSMSpeciesToSpeciesInv
import AFTD.Kb.Physics.MSSMChargesHdToSpeciesInv
import AFTD.Kb.Physics.MSSMChargesHuToSpeciesInv
import AFTD.Kb.Physics.MSSMChargesToSMPlusH
import AFTD.Kb.Physics.MSSMACCsAccGrav
import AFTD.Kb.Physics.MSSMACCsAccSU2
import AFTD.Kb.Physics.MSSMACCsAccSU3
import AFTD.Kb.Physics.MSSMACCsAccYY
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
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.SMRHNPlusU1
import AFTD.Kb.GameTheoryEconomics.LxvVal
import AFTD.Kb.GameTheoryEconomics.MatrixGameToStrategicGame

/-!
# MSSMACC.doublePoint_Y₃_Y₃

Topic: quantum_field_theory   Node: 804898a57769

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.doublePoint_Y₃_Y₃`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Y3.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMACC.doublePoint_Y₃_Y₃
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
lemma MSSMACC.doublePoint_Y₃_Y₃ (R : MSSMACC.LinSols) :
    cubeTriLin Y₃.val Y₃.val R.val = 0 := by
  simp only [cubeTriLin, TriLinearSymm.mk₃_toFun_apply_apply, cubeTriLinToFun]
  erw [Fin.sum_univ_three]
  rw [Y₃_val]
  rw [Y₃AsCharge]
  repeat rw [toSMSpecies_toSpecies_inv]
  rw [Hd_toSpecies_inv, Hu_toSpecies_inv]
  simp only [mul_one, Fin.isValue, toSMSpecies_apply, one_mul, mul_neg, neg_mul, neg_neg, mul_zero,
    zero_mul, add_zero, Hd_apply, Fin.reduceFinMk, Hu_apply]
  have hLin := R.linearSol
  simp only [MSSMACC_linearACCs] at hLin
  have h3 := hLin ⟨3, by simp⟩
  simp only [accYY, LinearMap.coe_mk, AddHom.coe_mk] at h3
  erw [Fin.sum_univ_three] at h3
  simp only [Fin.isValue, toSMSpecies_apply, Nat.reduceMul, Hd_apply, Fin.reduceFinMk,
    Hu_apply] at h3
  linear_combination (norm := ring_nf) 6 * h3
