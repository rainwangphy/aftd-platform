import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.MSSMACCsAccQuad
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.MSSMACCsAccCube
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.MSSMACCAnomalyFreeQuadMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction

/-!
# MSSMACC.AnomalyFreeMk'

Topic: quantum_field_theory   Node: d4c0cf7cee3c

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.AnomalyFreeMk'`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A `Sol` from a `LinSol` satisfying the quadratic and cubic ACCs.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
open MSSMACCs in
open MSSMCharges in
/-- A `Sol` from a `LinSol` satisfying the quadratic and cubic ACCs. -/
@[simp]
def MSSMACC.AnomalyFreeMk' (S : MSSMACC.LinSols) (hquad : accQuad S.val = 0)
    (hcube : accCube S.val = 0) : MSSMACC.Sols :=
  ⟨⟨S, by
    intro i
    match i with
    | ⟨0, _⟩ => exact hquad⟩, hcube⟩
