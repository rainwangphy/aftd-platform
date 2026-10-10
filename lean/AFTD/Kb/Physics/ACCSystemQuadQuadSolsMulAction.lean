import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.HomogeneousQuadraticMapSmul
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsExt
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# ACCSystemQuad.quadSolsMulAction

Topic: quantum_field_theory   Node: b7e1c092cdd9

Provenance: formalization of a published result. Source: Physlib, `ACCSystemQuad.quadSolsMulAction`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An instance giving the properties and structures to define an action of `ℚ` on `QuadSols`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An instance giving the properties and structures to define an action of `ℚ` on `QuadSols`. -/
instance ACCSystemQuad.quadSolsMulAction (χ : ACCSystemQuad) : MulAction ℚ χ.QuadSols where
  smul a S := ⟨a • S.toLinSols, fun _ ↦ by erw [(χ.quadraticACCs _).map_smul, S.quadSol _,
    mul_zero]⟩
  mul_smul a b S := QuadSols.ext (mul_smul _ _ _)
  one_smul S := QuadSols.ext (one_smul _ _)
