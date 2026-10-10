import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.SMSMNoGrav
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.SMACCsAccQuad
import AFTD.Kb.Physics.SMACCsAccCube
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
# SM.SMNoGrav.linearToQuad

Topic: quantum_field_theory   Node: 249fe1aa969d

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.linearToQuad`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An element of `AnomalyFreeLinear` which satisfies the quadratic ACCs gives us a element of `AnomalyFreeQuad`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SM in
open SMCharges in
open SMACCs in
open BigOperators in
variable {n : ℕ} in
/-- An element of `AnomalyFreeLinear` which satisfies the quadratic ACCs gives us a element of `AnomalyFreeQuad`. -/
def SM.SMNoGrav.linearToQuad (S : (SMNoGrav n).LinSols) : (SMNoGrav n).QuadSols :=
  ⟨S, by
    intro i
    exact Fin.elim0 i⟩
