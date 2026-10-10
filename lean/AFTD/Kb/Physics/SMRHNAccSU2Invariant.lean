import AFTD.Prelude
import AFTD.Kb.Physics.SMRHNPermGroup
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMNuACCsAccSU2
import AFTD.Kb.Physics.SMRHNInstGroupPermGroup
import AFTD.Kb.Physics.SMRHNRepCharges
import AFTD.Kb.Physics.SMNuACCsAccSU2Ext
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.SMNuChargesToSpecies
import AFTD.Kb.Physics.SMNuChargesToSpeciesEquiv
import AFTD.Kb.Physics.SMRHNChargeMap
import AFTD.Kb.Physics.SMRHNToSpeciesSumInvariant
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMRHN.accSU2_invariant

Topic: quantum_field_theory   Node: 9e0bb81a4d5d

Provenance: formalization of a published result. Source: Physlib, `SMRHN.accSU2_invariant`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMRHN.accSU2_invariant
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMRHN in
open Nat in
open Finset in
open SMνCharges in
open SMνACCs in
open BigOperators in
variable {n : ℕ} in
set_option backward.isDefEq.respectTransparency false in
lemma SMRHN.accSU2_invariant (f : PermGroup n) (S : (SMνCharges n).Charges) :
    accSU2 (repCharges f S) = accSU2 S :=
  accSU2_ext (by simpa using toSpecies_sum_invariant 1 f S)
