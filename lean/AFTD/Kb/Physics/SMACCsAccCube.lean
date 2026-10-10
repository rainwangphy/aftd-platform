import AFTD.Prelude
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.TriLinearSymmToCubic
import AFTD.Kb.Physics.SMACCsCubeTriLin
import AFTD.Kb.Physics.SMACCsAccQuad
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMACCs.accCube

Topic: quantum_field_theory   Node: 9dd6e3dbf8e3

Provenance: formalization of a published result. Source: Physlib, `SMACCs.accCube`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The cubic acc.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMACCs in
open Nat in
open BigOperators in
open SMCharges in
variable {n : ℕ} in
/-- The cubic acc. -/
@[simp]
def SMACCs.accCube : HomogeneousCubic (SMCharges n).Charges := cubeTriLin.toCubic
