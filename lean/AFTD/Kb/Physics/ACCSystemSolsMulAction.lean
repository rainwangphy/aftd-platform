import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.HomogeneousCubic
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousCubicInstFun
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.HomogeneousCubicMapSmul
import AFTD.Kb.Physics.ACCSystemSolsExt
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup

/-!
# ACCSystem.solsMulAction

Topic: quantum_field_theory   Node: 8cbcabc0979a

Provenance: formalization of a published result. Source: Physlib, `ACCSystem.solsMulAction`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An instance giving the properties and structures to define an action of `ℚ` on `Sols`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An instance giving the properties and structures to define an action of `ℚ` on `Sols`. -/
instance ACCSystem.solsMulAction (χ : ACCSystem) : MulAction ℚ χ.Sols where
  smul a S := ⟨a • S.toQuadSols, by
    erw [(χ.cubicACC).map_smul, S.cubicSol]
    exact Rat.mul_zero (a ^ 3)⟩
  mul_smul a b S := Sols.ext (mul_smul _ _ _)
  one_smul S := Sols.ext (one_smul _ _)
