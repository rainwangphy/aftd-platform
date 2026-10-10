import AFTD.Prelude
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.BiLinearSymmMk2
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.MSSMSpecies
import AFTD.Kb.Physics.MSSMChargesQ
import AFTD.Kb.Physics.MSSMChargesU
import AFTD.Kb.Physics.MSSMChargesD
import AFTD.Kb.Physics.MSSMChargesL
import AFTD.Kb.Physics.MSSMChargesE
import AFTD.Kb.Physics.MSSMChargesHd
import AFTD.Kb.Physics.MSSMChargesHu
import AFTD.Kb.Physics.MSSMChargesToSMPlusH
import AFTD.Kb.Physics.MSSMChargesToSMSpecies
import AFTD.Kb.Physics.MSSMChargesSumMSSMSpeciesNumberChargesEqExpand
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.GameTheoryEconomics.LxvVal

/-!
# MSSMACCs.quadBiLin

Topic: quantum_field_theory   Node: 74e774834bdb

Provenance: formalization of a published result. Source: Physlib, `MSSMACCs.quadBiLin`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The symmetric bilinear function used to define the quadratic ACC.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
open MSSMCharges in
set_option backward.isDefEq.respectTransparency false in
/-- The symmetric bilinear function used to define the quadratic ACC. -/
@[simps!]
def MSSMACCs.quadBiLin : BiLinearSymm MSSMCharges.Charges := BiLinearSymm.mk₂
  (fun (S, T) => ∑ i, (Q S i * Q T i + (- 2) * (U S i * U T i) +
    D S i * D T i + (- 1) * (L S i * L T i) + E S i * E T i) +
    (- Hd S * Hd T + Hu S * Hu T))
  (by
    intro a S T
    simp only
    rw [mul_add]
    congr 1
    · rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro i
      repeat rw [map_smul]
      simp only [HSMul.hSMul, SMul.smul, toSMSpecies_apply, Fin.isValue, neg_mul, one_mul]
      ring
    · simp only [map_smul, Hd_apply, Fin.reduceFinMk, Fin.isValue, smul_eq_mul, neg_mul, Hu_apply]
      ring)
  (by
    intro S T R
    simp only
    rw [add_assoc, ← add_assoc (-Hd S * Hd R + Hu S * Hu R) _ _]
    rw [add_comm (-Hd S * Hd R + Hu S * Hu R) _]
    rw [add_assoc]
    rw [← add_assoc _ _ (-Hd S * Hd R + Hu S * Hu R + (-Hd T * Hd R + Hu T * Hu R))]
    congr 1
    · rw [← Finset.sum_add_distrib]
      apply Fintype.sum_congr
      intro i
      repeat rw [map_add]
      simp only [ACCSystemCharges.chargesAddCommMonoid_add, toSMSpecies_apply, Fin.isValue, neg_mul,
        one_mul]
      ring
    · rw [Hd.map_add, Hu.map_add]
      ring)
  (by
    intro S L
    simp only [toSMSpecies_apply, Fin.isValue, neg_mul, one_mul, Hd_apply, Fin.reduceFinMk,
      Hu_apply]
    congr 1
    · simp only [reduceMul, Fin.isValue, sum_MSSMSpecies_numberCharges_eq_expand]
      ring
    · ring)
