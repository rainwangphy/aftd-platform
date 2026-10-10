import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.SMNuACCsAccGrav
import AFTD.Kb.Physics.SMNuACCsAccSU2
import AFTD.Kb.Physics.SMNuACCsAccSU3
import AFTD.Kb.Physics.SMNuACCsAccYY
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.SMNuSpecies
import AFTD.Kb.Physics.SMNuChargesQ
import AFTD.Kb.Physics.BiLinearSymmToHomogeneousQuad
import AFTD.Kb.Physics.SMNuACCsQuadBiLin
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.SMRHNRepCharges
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
import AFTD.Kb.Physics.ACCSystemGroupActionInstGroupGroup
import AFTD.Kb.Physics.ACCSystemGroupActionQuadSolAction
import AFTD.Kb.Physics.ACCSystemGroupActionSolAction

/-!
# SMRHN.PlusU1

Topic: quantum_field_theory   Node: 016ce9ba8bbc

Provenance: formalization of a published result. Source: Physlib, `SMRHN.PlusU1`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/PlusU1/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The ACC system for the SM plus RHN with an additional U1.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνCharges in
open SMνACCs in
open BigOperators in
/-- The ACC system for the SM plus RHN with an additional U1. -/
@[simps!]
def SMRHN.PlusU1 (n : ℕ) : ACCSystem where
  toACCSystemCharges := SMνCharges n
  numberLinear := 4
  linearACCs := fun i =>
    match i with
    | 0 => @accGrav n
    | 1 => accSU2
    | 2 => accSU3
    | 3 => accYY
  numberQuadratic := 1
  quadraticACCs := fun i =>
    match i with
    | 0 => accQuad
  cubicACC := accCube
