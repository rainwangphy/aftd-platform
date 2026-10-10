import AFTD.Prelude
import AFTD.Kb.Physics.SMPermGroup
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMChargeMap
import AFTD.Kb.Physics.SMInstGroupPermGroup
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.SMChargesToSpecies
import AFTD.Kb.Physics.SMChargesChargesEqToSpeciesEq
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMChargesToSpeciesEquiv
import AFTD.Kb.Physics.SMChargesToSMSpeciesToSpeciesInv
import AFTD.Kb.Physics.SMACCsAccQuad
import AFTD.Kb.Physics.SMACCsAccCube
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SM.repCharges

Topic: quantum_field_theory   Node: 1f5cf131c78b

Provenance: formalization of a published result. Source: Physlib, `SM.repCharges`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The representation of `(permGroup n)` acting on the vector space of charges.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SM in
open Nat in
open Finset in
open SMCharges in
open BigOperators in
variable {n : ℕ} in
/-- The representation of `(permGroup n)` acting on the vector space of charges. -/
@[simp]
def SM.repCharges {n : ℕ} : Representation ℚ (PermGroup n) (SMCharges n).Charges where
  toFun f := chargeMap f⁻¹
  map_mul' f g := by
    simp only [PermGroup]
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    intro i
    simp only [Module.End.mul_apply]
    erw [toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv]
    rfl
  map_one' := by
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    intro i
    exact toSMSpecies_toSpecies_inv _ _
