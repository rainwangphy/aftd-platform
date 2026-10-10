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
import AFTD.Kb.Physics.MSSMChargesSumMSSMSpeciesNumberChargesEqExpand
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# MSSMACCs.accGrav

Topic: quantum_field_theory   Node: c9851d7a66fc

Provenance: formalization of a published result. Source: Physlib, `MSSMACCs.accGrav`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The gravitational anomaly equation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
open MSSMCharges in
set_option backward.isDefEq.respectTransparency false in
/-- The gravitational anomaly equation. -/
def MSSMACCs.accGrav : MSSMCharges.Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (6 * Q S i + 3 * U S i + 3 * D S i
    + 2 * L S i + E S i + N S i) + 2 * (Hd S + Hu S)
  map_add' S T := by
    simp only [map_add, ACCSystemCharges.chargesAddCommMonoid_add,
      sum_MSSMSpecies_numberCharges_eq_expand]
    ring
  map_smul' a S := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    simp only [HSMul.hSMul, SMul.smul, sum_MSSMSpecies_numberCharges_eq_expand]
    ring
