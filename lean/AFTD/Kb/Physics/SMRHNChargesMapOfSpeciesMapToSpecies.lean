import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.SMNuChargesToSpecies
import AFTD.Kb.Physics.SMRHNChargesMapOfSpeciesMap
import AFTD.Kb.Physics.SMNuChargesToSMSpeciesToSpeciesInv
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMRHN.chargesMapOfSpeciesMap_toSpecies

Topic: quantum_field_theory   Node: 1d4f474f8dfc

Provenance: formalization of a published result. Source: Physlib, `SMRHN.chargesMapOfSpeciesMap_toSpecies`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/FamilyMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMRHN.chargesMapOfSpeciesMap_toSpecies
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνCharges in
open BigOperators in
lemma SMRHN.chargesMapOfSpeciesMap_toSpecies {n m : ℕ}
    (f : (SMνSpecies n).Charges →ₗ[ℚ] (SMνSpecies m).Charges)
    (S : (SMνCharges n).Charges) (j : Fin 6) :
    toSpecies j (chargesMapOfSpeciesMap f S) = (LinearMap.comp f (toSpecies j)) S :=
  toSMSpecies_toSpecies_inv _ _
