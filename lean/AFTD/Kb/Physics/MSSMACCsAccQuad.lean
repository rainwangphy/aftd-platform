import AFTD.Prelude
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.BiLinearSymmToHomogeneousQuad
import AFTD.Kb.Physics.MSSMACCsQuadBiLin
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# MSSMACCs.accQuad

Topic: quantum_field_theory   Node: 3c1e884481d2

Provenance: formalization of a published result. Source: Physlib, `MSSMACCs.accQuad`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The quadratic ACC.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
open MSSMCharges in
/-- The quadratic ACC. -/
@[simp]
def MSSMACCs.accQuad : HomogeneousQuadratic MSSMCharges.Charges := quadBiLin.toHomogeneousQuad
