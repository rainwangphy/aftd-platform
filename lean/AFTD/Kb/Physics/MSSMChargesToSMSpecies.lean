import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.MSSMSpecies
import AFTD.Kb.Physics.MSSMChargesToSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.MSSMChargesToSMPlusH
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# MSSMCharges.toSMSpecies

Topic: quantum_field_theory   Node: be09535c9fc2

Provenance: formalization of a published result. Source: Physlib, `MSSMCharges.toSMSpecies`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a given `i ∈ Fin 6` the projection of `MSSMCharges.charges` down to the corresponding SM species of charges.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
/-- For a given `i ∈ Fin 6` the projection of `MSSMCharges.charges` down to the corresponding SM species of charges. -/
@[simps!]
def MSSMCharges.toSMSpecies (i : Fin 6) : MSSMCharges.Charges →ₗ[ℚ] MSSMSpecies.Charges where
  toFun S := (Prod.fst ∘ toSpecies) S i
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl
