import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.MSSMACCsCubeTriLinToFun
import AFTD.Kb.Physics.MSSMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.MSSMChargesQ
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.MSSMChargesSumMSSMSpeciesNumberChargesEqExpand
import AFTD.Kb.Physics.MSSMChargesU
import AFTD.Kb.Physics.MSSMChargesD
import AFTD.Kb.Physics.MSSMChargesL
import AFTD.Kb.Physics.MSSMChargesE
import AFTD.Kb.Physics.MSSMChargesN
import AFTD.Kb.Physics.MSSMChargesHd
import AFTD.Kb.Physics.MSSMChargesHu
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# MSSMACCs.cubeTriLinToFun_swap2

Topic: quantum_field_theory   Node: b771e8f4347f

Provenance: formalization of a published result. Source: Physlib, `MSSMACCs.cubeTriLinToFun_swap2`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MSSMACCs.cubeTriLinToFun_swap2
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
open MSSMCharges in
lemma MSSMACCs.cubeTriLinToFun_swap2 (S T R : MSSMCharges.Charges) :
    cubeTriLinToFun (S, T, R) = cubeTriLinToFun (S, R, T) := by
  simp only [cubeTriLinToFun, sum_MSSMSpecies_numberCharges_eq_expand]
  ring
