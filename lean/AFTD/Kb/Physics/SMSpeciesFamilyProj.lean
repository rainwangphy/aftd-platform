import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SM.speciesFamilyProj

Topic: quantum_field_theory   Node: 775fb11c019b

Provenance: formalization of a published result. Source: Physlib, `SM.speciesFamilyProj`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/FamilyMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The projection of the `m`-family charges onto the first `n`-family charges for species.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
/-- The projection of the `m`-family charges onto the first `n`-family charges for species. -/
@[simps!]
def SM.speciesFamilyProj {m n : ℕ} (h : n ≤ m) :
    (SMSpecies m).Charges →ₗ[ℚ] (SMSpecies n).Charges where
  toFun S := S ∘ Fin.castLE h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
