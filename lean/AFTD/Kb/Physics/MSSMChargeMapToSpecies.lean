import AFTD.Prelude
import AFTD.Kb.Physics.MSSMPermGroup
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.MSSMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.MSSMChargesToSMSpecies
import AFTD.Kb.Physics.MSSMChargeMap
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.MSSMChargesToSMSpeciesToSpeciesInv
import AFTD.Kb.Physics.MSSMChargesToSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.MSSMInstGroupPermGroup

/-!
# MSSM.chargeMap_toSpecies

Topic: quantum_field_theory   Node: 5a591c2efdf4

Provenance: formalization of a published result. Source: Physlib, `MSSM.chargeMap_toSpecies`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSM.chargeMap_toSpecies
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open Finset in
open MSSMCharges in
open BigOperators in
lemma MSSM.chargeMap_toSpecies (f : PermGroup) (S : MSSMCharges.Charges) (j : Fin 6) :
    toSMSpecies j (chargeMap f S) = toSMSpecies j S ∘ f j :=
  toSMSpecies_toSpecies_inv _ _
