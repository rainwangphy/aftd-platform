import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMChargesToSpeciesEquiv
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMCharges.toSpecies

Topic: quantum_field_theory   Node: 545bfdf51f98

Provenance: formalization of a published result. Source: Physlib, `SMCharges.toSpecies`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a given `i ∈ Fin 5`, the projection of a charge onto that species.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMCharges in
open Nat in
open BigOperators in
variable {n : ℕ} in
/-- For a given `i ∈ Fin 5`, the projection of a charge onto that species. -/
@[simps!]
def SMCharges.toSpecies (i : Fin 5) : (SMCharges n).Charges →ₗ[ℚ] (SMSpecies n).Charges where
  toFun S := toSpeciesEquiv S i
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl
