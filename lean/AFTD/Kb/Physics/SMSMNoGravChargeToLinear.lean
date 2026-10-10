import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.SMSMNoGrav
import AFTD.Kb.Physics.SMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMACCsAccSU2
import AFTD.Kb.Physics.SMACCsAccSU3
import AFTD.Kb.Physics.ACCSystemLinearLinSols
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
# SM.SMNoGrav.chargeToLinear

Topic: quantum_field_theory   Node: 5d6ba651ea43

Provenance: formalization of a published result. Source: Physlib, `SM.SMNoGrav.chargeToLinear`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/AnomalyCancellation/NoGrav/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An element of `charges` which satisfies the linear ACCs gives us a element of `AnomalyFreeLinear`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SM in
open SMCharges in
open SMACCs in
open BigOperators in
variable {n : ℕ} in
/-- An element of `charges` which satisfies the linear ACCs gives us a element of `AnomalyFreeLinear`. -/
def SM.SMNoGrav.chargeToLinear (S : (SMNoGrav n).Charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) :
    (SMNoGrav n).LinSols :=
  ⟨S, by
    intro i
    match i with
    | ⟨0, _⟩ => exact hSU2
    | ⟨1, _⟩ => exact hSU3⟩
