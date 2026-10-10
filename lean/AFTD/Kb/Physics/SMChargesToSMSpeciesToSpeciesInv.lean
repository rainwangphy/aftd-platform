import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMChargesToSpecies
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMChargesToSpeciesEquiv
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMCharges.toSMSpecies_toSpecies_inv

Topic: quantum_field_theory   Node: d80e7c9b99b9

Provenance: formalization of a published result. Source: Physlib, `SMCharges.toSMSpecies_toSpecies_inv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMCharges.toSMSpecies_toSpecies_inv
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMCharges in
open Nat in
open BigOperators in
variable {n : ℕ} in
set_option backward.isDefEq.respectTransparency false in
lemma SMCharges.toSMSpecies_toSpecies_inv (i : Fin 5) (f : Fin 5 → Fin n → ℚ) :
    (toSpecies i) (toSpeciesEquiv.symm f) = f i := by
  change (toSpeciesEquiv ∘ toSpeciesEquiv.symm) _ i= f i
  simp
