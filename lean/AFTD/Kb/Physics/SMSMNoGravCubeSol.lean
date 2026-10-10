import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.SMSMNoGrav
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.SMACCsAccCube
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.SMACCsAccQuad
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.SMRHNSMNoGravCubeSol
import AFTD.Kb.Physics.SMRHNSMCubeSol

/-!
# SM.SMNoGrav.cubeSol

Topic: quantum_field_theory   Node: 9b2a24b9f9a1

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.cubeSol`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The charges in `(SMNoGrav n).Sols` satisfy the cubic anomaly-equation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SM in
open SMCharges in
open SMACCs in
open BigOperators in
variable {n : ℕ} in
/-- The charges in `(SMNoGrav n).Sols` satisfy the cubic anomaly-equation. -/
lemma SM.SMNoGrav.cubeSol (S : (SMNoGrav n).Sols) : accCube S.val = 0 := S.cubicSol
