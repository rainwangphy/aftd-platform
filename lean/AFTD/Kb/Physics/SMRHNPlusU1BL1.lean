import AFTD.Prelude
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.SMRHNPlusU1
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.SMRHNPlusU1QuadSol
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.SMRHNRepCharges
import AFTD.Kb.Physics.BiLinearSymmInstFun
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
# SMRHN.PlusU1.BL₁

Topic: quantum_field_theory   Node: a83403f7bf7e

Provenance: formalization of a published result. Source: Physlib, `SMRHN.PlusU1.BL₁`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/PlusU1/BMinusL.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

$B - L$ in the 1-family case.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMRHN in
open SMνCharges in
open SMνACCs in
open BigOperators in
variable {n : ℕ} in
/-- $B - L$ in the 1-family case. -/
@[simps!]
def SMRHN.PlusU1.BL₁ : (PlusU1 1).Sols where
  val := fun i =>
    match i with
    | (0 : Fin 6) => 1
    | (1 : Fin 6) => -1
    | (2 : Fin 6) => -1
    | (3 : Fin 6) => -3
    | (4 : Fin 6) => 3
    | (5 : Fin 6) => 3
  linearSol := by
    intro i
    match i with
    | ⟨0, _⟩ => with_unfolding_all rfl
    | ⟨1, _⟩ => with_unfolding_all rfl
    | ⟨2, _⟩ => with_unfolding_all rfl
    | ⟨3, _⟩ => with_unfolding_all rfl
  quadSol := by
    intro i
    match i with
    | ⟨0, _⟩ => with_unfolding_all rfl
  cubicSol := by with_unfolding_all rfl
