import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.SMSMNoGrav
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMACCsAccGrav
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.SMSpecies
import AFTD.Kb.Physics.SMChargesQ
import AFTD.Kb.Physics.SMSMNoGravOneAccGravQZero
import AFTD.Kb.Physics.SMSMNoGravOneAccGravQNeZero
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.SMACCsAccQuad
import AFTD.Kb.Physics.SMACCsAccCube
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction

/-!
# SM.SMNoGrav.One.accGravSatisfied

Topic: quantum_field_theory   Node: a94ea18f224c

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.One.accGravSatisfied`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/One/Lemmas.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Any solution to the 1-family ACCs without gravity satisfies the gravitational ACC.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMCharges in
open SMACCs in
open BigOperators in
/-- Any solution to the 1-family ACCs without gravity satisfies the gravitational ACC. -/
theorem SM.SMNoGrav.One.accGravSatisfied {S : (SMNoGrav 1).Sols} :
    accGrav S.val = 0 :=
  (em _).elim accGrav_Q_zero accGrav_Q_ne_zero
