import AFTD.Prelude
import AFTD.Kb.Physics.SMPermGroup
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMChargesToSpecies
import AFTD.Kb.Physics.SMInstGroupPermGroup
import AFTD.Kb.Physics.SMRepCharges
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMChargesToSMSpeciesToSpeciesInv
import AFTD.Kb.Physics.SMACCsAccQuad
import AFTD.Kb.Physics.SMACCsAccCube
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SM.repCharges_toSpecies

Topic: quantum_field_theory   Node: f15b5678dbad

Provenance: formalization of a published result. Source: Physlib, `SM.repCharges_toSpecies`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The species charges of a set of charges acted on by a family permutation is the permutation of those species charges with the corresponding part of the family permutation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SM in
open Nat in
open Finset in
open SMCharges in
open BigOperators in
variable {n : ℕ} in
/-- The species charges of a set of charges acted on by a family permutation is the permutation of those species charges with the corresponding part of the family permutation. -/
lemma SM.repCharges_toSpecies (f : PermGroup n) (S : (SMCharges n).Charges) (j : Fin 5) :
    toSpecies j (repCharges f S) = toSpecies j S ∘ f⁻¹ j :=
  toSMSpecies_toSpecies_inv _ _
