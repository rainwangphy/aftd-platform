import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACCY3
import AFTD.Kb.Physics.MSSMACCB3
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.MSSMACCsAccQuad
import AFTD.Kb.Physics.MSSMACCsAccCube
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk
import AFTD.Kb.Physics.MSSMACCAnomalyFreeQuadMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk'
import AFTD.Kb.Physics.MSSMACCAnomalyFreeMk''
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.TriLinearSymmInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction

/-!
# MSSMACC.lineY₃B₃Charges

Topic: quantum_field_theory   Node: 9075142a25e6

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.lineY₃B₃Charges`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/LineY3B3.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The line through $Y_3$ and $B_3$ as `LinSols`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
/-- The line through $Y_3$ and $B_3$ as `LinSols`. -/
def MSSMACC.lineY₃B₃Charges (a b : ℚ) : MSSMACC.LinSols := a • Y₃.1.1 + b • B₃.1.1
