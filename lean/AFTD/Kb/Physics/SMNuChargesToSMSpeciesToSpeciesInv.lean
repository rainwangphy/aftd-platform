import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMNuChargesToSpecies
import AFTD.Kb.Physics.SMNuChargesToSpeciesEquiv
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMνCharges.toSMSpecies_toSpecies_inv

Topic: quantum_field_theory   Node: 411a93b9f318

Provenance: formalization of a published result. Source: Physlib, `SMνCharges.toSMSpecies_toSpecies_inv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMνCharges.toSMSpecies_toSpecies_inv
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνCharges in
open Nat in
open BigOperators in
variable {n : ℕ} in
lemma SMνCharges.toSMSpecies_toSpecies_inv (i : Fin 6) (f : Fin 6 → Fin n → ℚ) :
    (toSpecies i) (toSpeciesEquiv.symm f) = f i := by
  change (toSpeciesEquiv ∘ toSpeciesEquiv.symm) _ i = f i
  simp
