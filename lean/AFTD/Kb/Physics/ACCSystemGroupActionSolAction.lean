import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemGroupAction
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemGroupActionInstGroupGroup
import AFTD.Kb.Physics.ACCSystemGroupActionQuadSolAction
import AFTD.Kb.Physics.ACCSystemSolsExt
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction

/-!
# ACCSystemGroupAction.solAction

Topic: quantum_field_theory   Node: b39d81d86307

Provenance: formalization of a published result. Source: Physlib, `ACCSystemGroupAction.solAction`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/GroupActions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The group action acting on solutions to the anomaly cancellation conditions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The group action acting on solutions to the anomaly cancellation conditions. -/
instance ACCSystemGroupAction.solAction {χ : ACCSystem} (G : ACCSystemGroupAction χ) : MulAction G.group χ.Sols where
  smul g S := ⟨G.quadSolAction.toFun _ _ S.1 g, by
    simp only [MulAction.toFun_apply]
    change χ.cubicACC (G.rep g S.val) = 0
    rw [G.cubicInvariant, S.cubicSol]⟩
  mul_smul f1 f2 S := by
    apply ACCSystem.Sols.ext
    change (G.rep.toFun (f1 * f2)) S.val = _
    rw [G.rep.map_mul']
    rfl
  one_smul S := by
    apply ACCSystem.Sols.ext
    change (G.rep.toFun 1) S.val = _
    rw [G.rep.map_one']
    rfl
