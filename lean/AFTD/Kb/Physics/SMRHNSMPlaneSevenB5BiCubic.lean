import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.SMRHNSM
import AFTD.Kb.Physics.SMNuCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.TriLinearSymm
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.SMNuACCsCubeTriLin
import AFTD.Kb.Physics.SMRHNSMPlaneSevenB
import AFTD.Kb.Physics.SMRHNSMPlaneSevenB5
import AFTD.Kb.Physics.SMRHNSMPlaneSevenB5Cubic
import AFTD.Kb.Physics.SMNuChargesToSpeciesEquiv
import AFTD.Kb.Physics.SMRHNSMPlaneSevenB0
import AFTD.Kb.Physics.SMRHNSMPlaneSevenB1
import AFTD.Kb.Physics.SMRHNSMPlaneSevenB2
import AFTD.Kb.Physics.SMRHNSMPlaneSevenB3
import AFTD.Kb.Physics.SMRHNSMPlaneSevenB4
import AFTD.Kb.Physics.SMRHNSMPlaneSevenB6
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.SMNuACCsAccQuad
import AFTD.Kb.Physics.SMNuACCsAccCube
import AFTD.Kb.Physics.SMRHNRepCharges
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.HomogeneousCubicInstFun
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
# SMRHN.SM.PlaneSeven.B₅_Bi_cubic

Topic: quantum_field_theory   Node: 8d7266e3a70c

Provenance: formalization of a published result. Source: Physlib, `SMRHN.SM.PlaneSeven.B₅_Bi_cubic`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Ordinary/DimSevenPlane.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SMRHN.SM.PlaneSeven.B₅_Bi_cubic
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SMνCharges in
open SMνACCs in
open BigOperators in
lemma SMRHN.SM.PlaneSeven.B₅_Bi_cubic {i : Fin 7} (hi : 5 ≠ i) (S : (SM 3).Charges) :
    cubeTriLin (B 5) (B i) S = 0 := by
  change cubeTriLin (B₅) (B i) S = 0
  rw [B₅_cubic]
  fin_cases i <;>
    first | exact absurd rfl hi | simp [B₀, B₁, B₂, B₃, B₄, B₆, Fin.divNat, Fin.modNat]
