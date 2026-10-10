import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemGroupAction
import AFTD.Kb.Physics.SMRHNSMNoGrav
import AFTD.Kb.Physics.SMRHNPermGroup
import AFTD.Kb.Physics.SMRHNInstGroupPermGroup
import AFTD.Kb.Physics.SMRHNRepCharges
import AFTD.Kb.Physics.SMRHNAccCubeInvariant
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.SMRHNSMNoGravChargeToLinear
import AFTD.Kb.Physics.SMRHNAccSU2Invariant
import AFTD.Kb.Physics.SMRHNAccSU3Invariant
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
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
import AFTD.Kb.Physics.ACCSystemGroupActionInstGroupGroup
import AFTD.Kb.Physics.ACCSystemGroupActionQuadSolAction
import AFTD.Kb.Physics.ACCSystemGroupActionSolAction

/-!
# SMRHN.SMNoGrav.perm

Topic: quantum_field_theory   Node: 340b78161cb8

Provenance: formalization of a published result. Source: Physlib, `SMRHN.SMNoGrav.perm`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/NoGrav/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The permutations acting on the ACC system corresponding to the SM with RHN, and no gravitational anomaly.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMRHN SMRHN.SMNoGrav in
open SMνCharges in
open SMνACCs in
open BigOperators in
variable {n : ℕ} in
/-- The permutations acting on the ACC system corresponding to the SM with RHN, and no gravitational anomaly. -/
def SMRHN.SMNoGrav.perm (n : ℕ) : ACCSystemGroupAction (SMNoGrav n) where
  group := PermGroup n
  groupInst := inferInstance
  rep := repCharges
  linearInvariant := by
    intro i
    match i with
    | ⟨0, _⟩ => exact accSU2_invariant
    | ⟨1, _⟩ => exact accSU3_invariant
  quadInvariant := by
    intro i
    simp only [SMNoGrav_numberQuadratic] at i
    exact Fin.elim0 i
  cubicInvariant := accCube_invariant
