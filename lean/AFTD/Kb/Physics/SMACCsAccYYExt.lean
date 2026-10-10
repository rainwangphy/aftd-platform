import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMChargesToSpecies
import AFTD.Kb.Physics.SMACCsAccYY
import AFTD.Kb.Physics.SMChargesToSpeciesEquiv
import AFTD.Kb.Physics.SMChargesQ
import AFTD.Kb.Physics.SMChargesU
import AFTD.Kb.Physics.SMChargesD
import AFTD.Kb.Physics.SMChargesL
import AFTD.Kb.Physics.SMChargesE
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMACCs.accYY_ext

Topic: quantum_field_theory   Node: 7d0b16014c79

Provenance: formalization of a published result. Source: Physlib, `SMACCs.accYY_ext`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Extensionality lemma for `accYY`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMACCs in
open Nat in
open BigOperators in
open SMCharges in
variable {n : ℕ} in
set_option backward.isDefEq.respectTransparency false in
/-- Extensionality lemma for `accYY`. -/
lemma SMACCs.accYY_ext {S T : (SMCharges n).Charges}
    (hj : ∀ (j : Fin 5), ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accYY S = accYY T := by
  simp only [accYY, toSpecies_apply, Fin.isValue, LinearMap.coe_mk,
    AddHom.coe_mk]
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]
  simp_all
