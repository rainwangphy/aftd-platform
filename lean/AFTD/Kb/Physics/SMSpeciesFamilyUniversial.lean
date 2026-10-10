import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.SMRHNSpeciesFamilyUniversial

/-!
# SM.speciesFamilyUniversial

Topic: quantum_field_theory   Node: 45c53fb4fd1f

Provenance: formalization of a published result. Source: Physlib, `SM.speciesFamilyUniversial`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/FamilyMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For species, the embedding of the `1`-family charges into the `n`-family charges in a universal manner.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators in
/-- For species, the embedding of the `1`-family charges into the `n`-family charges in a universal manner. -/
@[simps!]
def SM.speciesFamilyUniversial (n : ℕ) :
    (SMSpecies 1).Charges →ₗ[ℚ] (SMSpecies n).Charges where
  toFun S _ := S ⟨0, Nat.zero_lt_succ 0⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
