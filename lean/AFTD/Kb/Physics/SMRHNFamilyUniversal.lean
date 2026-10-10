import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMRHNChargesMapOfSpeciesMap
import AFTD.Kb.Physics.SMRHNSpeciesFamilyUniversial
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMRHN.familyUniversal

Topic: quantum_field_theory   Node: 030fdeb8d3a6

Provenance: formalization of a published result. Source: Physlib, `SMRHN.familyUniversal`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/FamilyMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The embedding of the `1`-family charges into the `n`-family charges in a universal manner.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνCharges in
open BigOperators in
/-- The embedding of the `1`-family charges into the `n`-family charges in a universal manner. -/
def SMRHN.familyUniversal (n : ℕ) : (SMνCharges 1).Charges →ₗ[ℚ] (SMνCharges n).Charges :=
  chargesMapOfSpeciesMap (speciesFamilyUniversial n)
