import AFTD.Prelude
import AFTD.Kb.Physics.SMPermGroup
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMACCsAccSU2
import AFTD.Kb.Physics.SMInstGroupPermGroup
import AFTD.Kb.Physics.SMRepCharges
import AFTD.Kb.Physics.SMACCsAccSU2Ext
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.SMChargesToSpecies
import AFTD.Kb.Physics.SMChargesToSpeciesEquiv
import AFTD.Kb.Physics.SMChargeMap
import AFTD.Kb.Physics.SMToSpeciesSumInvariant
import AFTD.Kb.Physics.SMACCsAccQuad
import AFTD.Kb.Physics.SMACCsAccCube
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SM.accSU2_invariant

Topic: quantum_field_theory   Node: fd48d4f110f9

Provenance: formalization of a published result. Source: Physlib, `SM.accSU2_invariant`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `SU(2)` anomaly equation is invariant under family permutations.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SM in
open Nat in
open Finset in
open SMCharges in
open SMACCs in
open BigOperators in
variable {n : ℕ} in
set_option backward.isDefEq.respectTransparency false in
/-- The `SU(2)` anomaly equation is invariant under family permutations. -/
lemma SM.accSU2_invariant (f : PermGroup n) (S : (SMCharges n).Charges) :
    accSU2 (repCharges f S) = accSU2 S := accSU2_ext
  (by simpa using toSpecies_sum_invariant 1 f S)
