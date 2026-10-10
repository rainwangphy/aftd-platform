import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.MSSMACC
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.BiLinearSymm
import AFTD.Kb.Physics.BiLinearSymmInstFun
import AFTD.Kb.Physics.MSSMACCDot
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.MSSMACCY3
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.MSSMACCB3
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.BiLinearSymmMapAdd2
import AFTD.Kb.Physics.BiLinearSymmMapSmul2
import AFTD.Kb.Physics.MSSMACCAnomalyFreePerp
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
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction

/-!
# MSSMACC.proj

Topic: quantum_field_theory   Node: b3b0c3a0e297

Provenance: formalization of a published result. Source: Physlib, `MSSMACC.proj`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/OrthogY3B3/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The projection of an object in `MSSMACC.AnomalyFreeLinear` onto the subspace orthogonal to `Y₃` and`B₃`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MSSMCharges in
open MSSMACCs in
open BigOperators in
set_option backward.isDefEq.respectTransparency false in
/-- The projection of an object in `MSSMACC.AnomalyFreeLinear` onto the subspace orthogonal to `Y₃` and`B₃`. -/
def MSSMACC.proj (T : MSSMACC.LinSols) : MSSMACC.AnomalyFreePerp :=
  ⟨(dot B₃.val T.val - dot Y₃.val T.val) • Y₃.1.1
  + (dot Y₃.val T.val - 2 * dot B₃.val T.val) • B₃.1.1
  + dot Y₃.val B₃.val • T,
  by
    change dot _ (_ • Y₃.val + _ • B₃.val + _ • T.val) = 0
    rw [dot.map_add₂, dot.map_add₂]
    rw [dot.map_smul₂, dot.map_smul₂, dot.map_smul₂]
    rw [show dot Y₃.val B₃.val = 108 by with_unfolding_all rfl]
    rw [show dot Y₃.val Y₃.val = 216 by with_unfolding_all rfl]
    ring,
  by
    change dot _ (_ • Y₃.val + _ • B₃.val + _ • T.val) = 0
    rw [dot.map_add₂, dot.map_add₂]
    rw [dot.map_smul₂, dot.map_smul₂, dot.map_smul₂]
    rw [show dot Y₃.val B₃.val = 108 by with_unfolding_all rfl]
    rw [show dot B₃.val Y₃.val = 108 by with_unfolding_all rfl]
    rw [show dot B₃.val B₃.val = 108 by with_unfolding_all rfl]
    ring⟩
