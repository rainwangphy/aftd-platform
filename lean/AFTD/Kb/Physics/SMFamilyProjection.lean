import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMChargesMapOfSpeciesMap
import AFTD.Kb.Physics.SMSpeciesFamilyProj
import AFTD.Kb.Physics.SMACCsAccQuad
import AFTD.Kb.Physics.SMACCsAccCube
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SM.familyProjection

Topic: quantum_field_theory   Node: 2f7ded66f288

Provenance: formalization of a published result. Source: Physlib, `SM.familyProjection`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/FamilyMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The projection of the `m`-family charges onto the first `n`-family charges.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMCharges in
open BigOperators in
/-- The projection of the `m`-family charges onto the first `n`-family charges. -/
def SM.familyProjection {m n : ℕ} (h : n ≤ m) : (SMCharges m).Charges →ₗ[ℚ] (SMCharges n).Charges :=
  chargesMapOfSpeciesMap (speciesFamilyProj h)
