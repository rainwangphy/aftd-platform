import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMChargesMapOfSpeciesMap
import AFTD.Kb.Physics.SMSpeciesFamilyUniversial
import AFTD.Kb.Physics.SMACCsAccQuad
import AFTD.Kb.Physics.SMACCsAccCube
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SM.familyUniversal

Topic: quantum_field_theory   Node: f12fd5041462

Provenance: formalization of a published result. Source: Physlib, `SM.familyUniversal`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/FamilyMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The embedding of the `1`-family charges into the `n`-family charges in a universal manner.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMCharges in
open BigOperators in
/-- The embedding of the `1`-family charges into the `n`-family charges in a universal manner. -/
def SM.familyUniversal (n : ℕ) : (SMCharges 1).Charges →ₗ[ℚ] (SMCharges n).Charges :=
  chargesMapOfSpeciesMap (speciesFamilyUniversial n)
