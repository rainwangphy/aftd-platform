import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMRHNChargesMapOfSpeciesMap
import AFTD.Kb.Physics.SMRHNSpeciesFamilyProj
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMRHN.familyProjection

Topic: quantum_field_theory   Node: 3de37e7367e2

Provenance: formalization of a published result. Source: Physlib, `SMRHN.familyProjection`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/FamilyMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The projection of the `m`-family charges onto the first `n`-family charges.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνCharges in
open BigOperators in
/-- The projection of the `m`-family charges onto the first `n`-family charges. -/
def SMRHN.familyProjection {m n : ℕ} (h : n ≤ m) : (SMνCharges m).Charges →ₗ[ℚ] (SMνCharges n).Charges :=
  chargesMapOfSpeciesMap (speciesFamilyProj h)
