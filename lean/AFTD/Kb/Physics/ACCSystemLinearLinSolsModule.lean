import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsExt
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# ACCSystemLinear.linSolsModule

Topic: quantum_field_theory   Node: 9b33691d8270

Provenance: formalization of a published result. Source: Physlib, `ACCSystemLinear.linSolsModule`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An instance providing the operations and properties for `LinSols` to form a module over `ℚ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An instance providing the operations and properties for `LinSols` to form a module over `ℚ`. -/
@[simps!]
instance ACCSystemLinear.linSolsModule (χ : ACCSystemLinear) : Module ℚ χ.LinSols where
  smul a S := ⟨a • S.val, fun _ ↦ by simp [(χ.linearACCs _).map_smul, S.linearSol _]⟩
  one_smul one_smul := LinSols.ext (χ.chargesModule.one_smul _)
  mul_smul a b S := LinSols.ext (χ.chargesModule.mul_smul _ _ _)
  smul_zero a := LinSols.ext (χ.chargesModule.smul_zero _)
  zero_smul S := LinSols.ext (χ.chargesModule.zero_smul _)
  smul_add a S T := LinSols.ext (χ.chargesModule.smul_add _ _ _)
  add_smul a b T:= LinSols.ext (χ.chargesModule.add_smul _ _ _)
