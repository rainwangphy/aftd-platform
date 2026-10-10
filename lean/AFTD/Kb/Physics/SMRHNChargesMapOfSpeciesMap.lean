import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.SMNuChargesToSpeciesEquiv
import AFTD.Kb.Physics.SMNuChargesToSpecies
import AFTD.Kb.Physics.SMNuChargesChargesEqToSpeciesEq
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.SMNuChargesToSMSpeciesToSpeciesInv
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMRHN.chargesMapOfSpeciesMap

Topic: quantum_field_theory   Node: 1fc79f4dbafe

Provenance: formalization of a published result. Source: Physlib, `SMRHN.chargesMapOfSpeciesMap`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/FamilyMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a map of for a generic species, the corresponding map for charges.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνCharges in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
/-- Given a map of for a generic species, the corresponding map for charges. -/
@[simps!]
def SMRHN.chargesMapOfSpeciesMap {n m : ℕ} (f : (SMνSpecies n).Charges →ₗ[ℚ] (SMνSpecies m).Charges) :
    (SMνCharges n).Charges →ₗ[ℚ] (SMνCharges m).Charges where
  toFun S := toSpeciesEquiv.symm (fun i => (LinearMap.comp f (toSpecies i)) S)
  map_add' S T := by
    rw [charges_eq_toSpecies_eq]
    intro i
    rw [map_add, toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv,
      map_add]
  map_smul' a S := by
    rw [charges_eq_toSpecies_eq]
    intro i
    rw [map_smul, toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv, map_smul]
    rfl
