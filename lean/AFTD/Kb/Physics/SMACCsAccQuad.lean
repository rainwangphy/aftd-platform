import AFTD.Prelude
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.BiLinearSymmToHomogeneousQuad
import AFTD.Kb.Physics.SMACCsQuadBiLin
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# SMACCs.accQuad

Topic: quantum_field_theory   Node: 449cc7bd4127

Provenance: formalization of a published result. Source: Physlib, `SMACCs.accQuad`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The quadratic anomaly cancellation condition.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMACCs in
open Nat in
open BigOperators in
open SMCharges in
variable {n : ℕ} in
/-- The quadratic anomaly cancellation condition. -/
@[simp]
def SMACCs.accQuad : HomogeneousQuadratic (SMCharges n).Charges :=
  (@quadBiLin n).toHomogeneousQuad
