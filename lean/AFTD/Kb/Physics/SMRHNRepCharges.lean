import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMRHNChargeMap
import AFTD.Kb.Physics.SMRHNPermGroup
import AFTD.Kb.Physics.SMRHNInstGroupPermGroup
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.SMNuChargesToSpecies
import AFTD.Kb.Physics.SMNuChargesChargesEqToSpeciesEq
import AFTD.Kb.Physics.SMNuChargesToSMSpeciesToSpeciesInv
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMNuChargesToSpeciesEquiv
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMRHN.repCharges

Topic: quantum_field_theory   Node: 96b623bd7e1a

Provenance: formalization of a published result. Source: Physlib, `SMRHN.repCharges`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The representation of `(permGroup n)` acting on the vector space of charges.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMRHN in
open Nat in
open Finset in
open SMνCharges in
open BigOperators in
variable {n : ℕ} in
set_option backward.isDefEq.respectTransparency false in
/-- The representation of `(permGroup n)` acting on the vector space of charges. -/
@[simp]
def SMRHN.repCharges {n : ℕ} : Representation ℚ (PermGroup n) (SMνCharges n).Charges where
  toFun f := chargeMap f⁻¹
  map_mul' f g := by
    simp only [PermGroup]
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    intro i
    simp only [chargeMap_apply, Pi.inv_apply, Module.End.mul_apply]
    repeat rw [toSMSpecies_toSpecies_inv]
    rfl
  map_one' := by
    refine LinearMap.ext fun S => ?_
    rw [charges_eq_toSpecies_eq]
    intro i
    exact toSMSpecies_toSpecies_inv _ _
