import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.MSSMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.MSSMChargesQ
import AFTD.Kb.Physics.MSSMChargesU
import AFTD.Kb.Physics.MSSMChargesD
import AFTD.Kb.Physics.MSSMChargesL
import AFTD.Kb.Physics.MSSMChargesE
import AFTD.Kb.Physics.MSSMChargesN
import AFTD.Kb.Physics.MSSMChargesHd
import AFTD.Kb.Physics.MSSMChargesHu
import AFTD.Kb.Physics.MSSMChargesToSMPlusH
import AFTD.Kb.Physics.MSSMChargesToSMSpecies
import AFTD.Kb.Physics.MSSMChargesSumMSSMSpeciesNumberChargesEqExpand
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.BiLinearSymmMk2
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.GameTheoryEconomics.LxvVal

/-!
# MSSMACC.dot

Topic: quantum_field_theory   Node: 19f39a8c2efe

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.dot`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The dot product on the vector space of charges.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
open MSSMCharges in
set_option backward.isDefEq.respectTransparency false in
/-- The dot product on the vector space of charges. -/
@[simps!]
def MSSMACC.dot : BiLinearSymm MSSMCharges.Charges := BiLinearSymm.mk₂
  (fun S => ∑ i, (Q S.1 i * Q S.2 i + U S.1 i * U S.2 i +
    D S.1 i * D S.2 i + L S.1 i * L S.2 i + E S.1 i * E S.2 i
    + N S.1 i * N S.2 i) + Hd S.1 * Hd S.2 + Hu S.1 * Hu S.2)
  (by
    intro a S T
    repeat rw [(toSMSpecies _).map_smul]
    rw [Hd.map_smul, Hu.map_smul]
    simp only [Fin.isValue, toSMSpecies_apply, reduceMul, sum_MSSMSpecies_numberCharges_eq_expand,
      Fin.zero_eta, Fin.mk_one, Hd_apply, Fin.reduceFinMk, smul_eq_mul, Hu_apply]
    simp only [HSMul.hSMul, SMul.smul, Fin.isValue, toSMSpecies_apply]
    ring)
  (by
    intro S1 S2 T
    simp only [map_add, ACCSystemCharges.chargesAddCommMonoid_add]
    simp only [toSMSpecies_apply, Fin.isValue, Hd_apply, Fin.reduceFinMk, Hu_apply]
    simp only [reduceMul, Fin.isValue, sum_MSSMSpecies_numberCharges_eq_expand, Fin.zero_eta,
      Fin.mk_one]
    simp only [Fin.isValue, Prod.mk_zero_zero, Prod.mk_one_one]
    ring)
  (by
    intro S T
    simp only [toSMSpecies_apply, Fin.isValue, Hd_apply, Fin.reduceFinMk, Hu_apply]
    simp only [reduceMul, Fin.isValue, sum_MSSMSpecies_numberCharges_eq_expand, Fin.zero_eta,
      Fin.mk_one]
    simp only [Fin.isValue, Prod.mk_zero_zero, Prod.mk_one_one]
    ring)
