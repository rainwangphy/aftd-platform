import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMChargesQ
import AFTD.Kb.Physics.SMChargesL
import AFTD.Kb.Physics.SMChargesToSpeciesEquiv
import AFTD.Kb.Physics.SMChargesToSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMACCs.accSU2

Topic: quantum_field_theory   Node: b41c88836385

Provenance: formalization of a published result. Source: Physlib, `SMACCs.accSU2`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `SU(2)` anomaly equation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
open SMCharges in
variable {n : ℕ} in
set_option backward.isDefEq.respectTransparency false in
/-- The `SU(2)` anomaly equation. -/
def SMACCs.accSU2 : (SMCharges n).Charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (3 * Q S i + L S i)
  map_add' S T := by
    repeat rw [map_add]
    simp only [ACCSystemCharges.chargesAddCommMonoid_add, toSpecies_apply,
      Fin.isValue, mul_add]
    repeat rw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    repeat rw [map_smul]
    simp only [ HSMul.hSMul, SMul.smul, toSpecies_apply, Fin.isValue,
      eq_ratCast, Rat.cast_eq_id, id_eq]
    repeat rw [Finset.sum_add_distrib]
    repeat rw [← Finset.mul_sum]
    --rw [show Rat.cast a = a from rfl]
    ring
