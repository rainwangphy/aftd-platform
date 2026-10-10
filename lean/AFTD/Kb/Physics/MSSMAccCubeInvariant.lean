import AFTD.Prelude
import AFTD.Kb.Physics.MSSMPermGroup
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.MSSMACCsAccCube
import AFTD.Kb.Physics.MSSMInstGroupPermGroup
import AFTD.Kb.Physics.MSSMRepCharges
import AFTD.Kb.Physics.MSSMACCsAccCubeExt
import AFTD.Kb.Physics.MSSMToSpeciesSumInvariant
import AFTD.Kb.Physics.MSSMHdInvariant
import AFTD.Kb.Physics.MSSMHuInvariant
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk''
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# MSSM.accCube_invariant

Topic: quantum_field_theory   Node: 6f49655d84cf

Provenance: formalization of a published result. Source: Physlib, `MSSM.accCube_invariant`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Permutations.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSM.accCube_invariant
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open Finset in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
lemma MSSM.accCube_invariant (f : PermGroup) (S : MSSMCharges.Charges) :
    accCube (repCharges f S) = accCube S :=
  accCube_ext
    (toSpecies_sum_invariant 3 f S)
    (Hd_invariant f S)
    (Hu_invariant f S)
