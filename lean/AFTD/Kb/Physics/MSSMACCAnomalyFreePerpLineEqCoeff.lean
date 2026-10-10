import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCDot
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.MSSMACCY3
import AFTD.Kb.Physics.MSSMACCB3
import AFTD.Kb.Physics.MSSMACCAlpha3
import AFTD.Kb.Physics.MSSMACCProj
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.MSSMACCsAccQuad
import AFTD.Kb.Physics.MSSMACCsAccCube
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk
import AFTD.Kb.Physics.MSSMACCAnomalyFreeQuadMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk''
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerpInstDecidableLineEqProp

/-!
# MSSMACC.AnomalyFreePerp.lineEqCoeff

Topic: quantum_field_theory   Node: 7bf5861c6ced

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.AnomalyFreePerp.lineEqCoeff`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/ToSols.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A rational which appears in `toSolNS` acting on sols, and which being zero is equivalent to satisfying `lineEqPropSol`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
/-- A rational which appears in `toSolNS` acting on sols, and which being zero is equivalent to satisfying `lineEqPropSol`. -/
def MSSMACC.AnomalyFreePerp.lineEqCoeff (T : MSSMACC.Sols) : ℚ := dot Y₃.val B₃.val * α₃ (proj T.1.1)
