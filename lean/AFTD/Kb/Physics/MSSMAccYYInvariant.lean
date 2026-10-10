import AFTD.Prelude
import AFTD.Kb.Physics.MSSMPermGroup
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.MSSMACCsAccYY
import AFTD.Kb.Physics.MSSMInstGroupPermGroup
import AFTD.Kb.Physics.MSSMRepCharges
import AFTD.Kb.Physics.MSSMACCsAccYYExt
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.MSSMSpecies
import AFTD.Kb.Physics.MSSMChargesToSMSpecies
import AFTD.Kb.Physics.MSSMChargesToSMPlusH
import AFTD.Kb.Physics.MSSMChargesSplitSMPlusH
import AFTD.Kb.Physics.MSSMChargesToSpeciesMaps'
import AFTD.Kb.Physics.MSSMChargeMap
import AFTD.Kb.Physics.MSSMToSpeciesSumInvariant
import AFTD.Kb.Physics.MSSMHdInvariant
import AFTD.Kb.Physics.MSSMHuInvariant
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# MSSM.accYY_invariant

Topic: quantum_field_theory   Node: 9921010a617d

Provenance: formalization of a published result. Source: Physlib, `MSSM.accYY_invariant`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSM.accYY_invariant
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open Finset in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
lemma MSSM.accYY_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    accYY (repCharges f S) = accYY S :=
  accYY_ext
    (by simpa using toSpecies_sum_invariant 1 f S)
    (Hd_invariant f S)
    (Hu_invariant f S)
