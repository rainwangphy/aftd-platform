import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMChargesToSpeciesEquiv
import AFTD.Kb.Physics.SMChargesToSpecies
import AFTD.Kb.Physics.SMChargesChargesEqToSpeciesEq
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.SMChargesToSMSpeciesToSpeciesInv
import AFTD.Kb.Physics.SMACCsAccQuad
import AFTD.Kb.Physics.SMACCsAccCube
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.SMRHNChargesMapOfSpeciesMap

/-!
# SM.chargesMapOfSpeciesMap

Topic: quantum_field_theory   Node: d8457f453ffb

Provenance: formalization of a published result. Source: Physlib, `SM.chargesMapOfSpeciesMap`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/FamilyMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a map of for a generic species, the corresponding map for charges.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMCharges in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
/-- Given a map of for a generic species, the corresponding map for charges. -/
@[simps!]
def SM.chargesMapOfSpeciesMap {n m : ℕ} (f : (SMSpecies n).Charges →ₗ[ℚ] (SMSpecies m).Charges) :
    (SMCharges n).Charges →ₗ[ℚ] (SMCharges m).Charges where
  toFun S := toSpeciesEquiv.symm (fun i => (LinearMap.comp f (toSpecies i)) S)
  map_add' S T := by
    rw [charges_eq_toSpecies_eq]
    intro i
    rw [map_add]
    rw [toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv]
    rw [map_add]
  map_smul' a S := by
    rw [charges_eq_toSpecies_eq]
    intro i
    rw [map_smul]
    rw [toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv]
    rw [map_smul]
    rfl
