import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemGroupAction
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemGroupActionInstGroupGroup
import AFTD.Kb.Physics.ACCSystemGroupActionLinSolRep
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsExt
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsMulAction

/-!
# ACCSystemGroupAction.quadSolAction

Topic: quantum_field_theory   Node: 24b39456a95f

Provenance: formalization of a published result. Source: Physlib, `ACCSystemGroupAction.quadSolAction`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/GroupActions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A multiplicative action of `G.group` on `quadSols`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option backward.isDefEq.respectTransparency false in
/-- A multiplicative action of `G.group` on `quadSols`. -/
instance ACCSystemGroupAction.quadSolAction {χ : ACCSystem} (G : ACCSystemGroupAction χ) :
    MulAction G.group χ.QuadSols where
  smul f S := ⟨G.linSolRep f S.1, by simp [linSolRep_apply_apply_val, G.quadInvariant, S.quadSol]⟩
  mul_smul f1 f2 S := by
    apply ACCSystemQuad.QuadSols.ext
    change (G.rep.toFun (f1 * f2)) S.val = _
    rw [G.rep.map_mul']
    rfl
  one_smul S := by
    apply ACCSystemQuad.QuadSols.ext
    change (G.rep.toFun 1) S.val = _
    rw [G.rep.map_one']
    rfl
