import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.MSSMSpecies
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.MSSMChargesQ
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
# MSSMACCs.cubeTriLinToFun

Topic: quantum_field_theory   Node: b9bdc3c17e05

Provenance: formalization of a published result. Source: Physlib, `MSSMACCs.cubeTriLinToFun`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The function underlying the symmetric trilinear form used to define the cubic ACC.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
open MSSMCharges in
/-- The function underlying the symmetric trilinear form used to define the cubic ACC. -/
def MSSMACCs.cubeTriLinToFun
    (S : MSSMCharges.Charges × MSSMCharges.Charges × MSSMCharges.Charges) : ℚ :=
  ∑ i, (6 * (Q S.1 i * Q S.2.1 i * Q S.2.2 i)
    + 3 * (U S.1 i * U S.2.1 i * U S.2.2 i)
    + 3 * (D S.1 i * D S.2.1 i * D S.2.2 i)
    + 2 * (L S.1 i * L S.2.1 i * L S.2.2 i)
    + E S.1 i * E S.2.1 i * E S.2.2 i
    + N S.1 i * N S.2.1 i * N S.2.2 i)
    + (2 * Hd S.1 * Hd S.2.1 * Hd S.2.2
    + 2 * Hu S.1 * Hu S.2.1 * Hu S.2.2)
