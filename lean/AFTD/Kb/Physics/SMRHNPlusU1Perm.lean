import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.SMRHNPlusU1
import AFTD.Kb.Physics.SMRHNPermGroup
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.SMRHNInstGroupPermGroup
import AFTD.Kb.Physics.SMRHNRepCharges
import AFTD.Kb.Physics.SMRHNPlusU1LinearToQuad
import AFTD.Kb.Physics.SMRHNAccQuadInvariant
import AFTD.Kb.Physics.SMRHNPlusU1ChargeToLinear
import AFTD.Kb.Physics.SMRHNAccGravInvariant
import AFTD.Kb.Physics.SMRHNAccSU2Invariant
import AFTD.Kb.Physics.SMRHNAccSU3Invariant
import AFTD.Kb.Physics.SMRHNAccYYInvariant
import AFTD.Kb.Physics.ACCSystemGroupAction
import AFTD.Kb.Physics.SMRHNAccCubeInvariant
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
# SMRHN.PlusU1.perm

Topic: quantum_field_theory   Node: a11c6c1c5f5e

Provenance: formalization of a published result. Source: Physlib, `SMRHN.PlusU1.perm`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/PlusU1/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The permutations acting on the ACC system corresponding to the SM with RHN.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMRHN SMRHN.PlusU1 in
open SMνCharges in
open SMνACCs in
open BigOperators in
variable {n : ℕ} in
/-- The permutations acting on the ACC system corresponding to the SM with RHN. -/
def SMRHN.PlusU1.perm (n : ℕ) : ACCSystemGroupAction (PlusU1 n) where
  group := PermGroup n
  groupInst := inferInstance
  rep := repCharges
  linearInvariant := by
    intro i
    match i with
    | ⟨0, _⟩ => exact accGrav_invariant
    | ⟨1, _⟩ => exact accSU2_invariant
    | ⟨2, _⟩ => exact accSU3_invariant
    | ⟨3, _⟩ => exact accYY_invariant
  quadInvariant := by
    intro i
    match i with
    | ⟨0, _⟩ => exact accQuad_invariant
  cubicInvariant := accCube_invariant
