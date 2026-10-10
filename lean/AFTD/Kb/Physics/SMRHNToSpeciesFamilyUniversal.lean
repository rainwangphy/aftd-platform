import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMNuChargesToSpecies
import AFTD.Kb.Physics.SMRHNFamilyUniversal
import AFTD.Kb.Physics.SMRHNChargesMapOfSpeciesMap
import AFTD.Kb.Physics.SMRHNSpeciesFamilyUniversial
import AFTD.Kb.Physics.SMRHNChargesMapOfSpeciesMapToSpecies
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMRHN.toSpecies_familyUniversal

Topic: quantum_field_theory   Node: 52306deb3fb9

Provenance: formalization of a published result. Source: Physlib, `SMRHN.toSpecies_familyUniversal`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/FamilyMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMRHN.toSpecies_familyUniversal
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνCharges in
open BigOperators in
lemma SMRHN.toSpecies_familyUniversal {n : ℕ} (j : Fin 6) (S : (SMνCharges 1).Charges)
    (i : Fin n) : toSpecies j (familyUniversal n S) i = toSpecies j S ⟨0, by simp⟩ := by
  rw [familyUniversal, chargesMapOfSpeciesMap_toSpecies]
  rfl
