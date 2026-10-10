import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMNuChargesToSpeciesEquiv
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMνCharges.toSpecies

Topic: quantum_field_theory   Node: def7d1b97c79

Provenance: formalization of a published result. Source: Physlib, `SMνCharges.toSpecies`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given an `i ∈ Fin 6`, the projection of charges onto a given species.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνCharges in
open Nat in
open BigOperators in
variable {n : ℕ} in
/-- Given an `i ∈ Fin 6`, the projection of charges onto a given species. -/
@[simps!]
def SMνCharges.toSpecies (i : Fin 6) : (SMνCharges n).Charges →ₗ[ℚ] (SMνSpecies n).Charges where
  toFun S := toSpeciesEquiv S i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
