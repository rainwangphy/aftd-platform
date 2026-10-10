import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMNuChargesToSpecies
import AFTD.Kb.Physics.SMNuChargesToSpeciesEquiv
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMνCharges.charges_eq_toSpecies_eq

Topic: quantum_field_theory   Node: 1aaa97c98c09

Provenance: formalization of a published result. Source: Physlib, `SMνCharges.charges_eq_toSpecies_eq`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMνCharges.charges_eq_toSpecies_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνCharges in
open Nat in
open BigOperators in
variable {n : ℕ} in
lemma SMνCharges.charges_eq_toSpecies_eq (S T : (SMνCharges n).Charges) :
    S = T ↔ ∀ i, toSpecies i S = toSpecies i T := by
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · exact fun i => congrArg (⇑(toSpecies i)) h
  · apply toSpeciesEquiv.injective
    exact funext (fun i => h i)
