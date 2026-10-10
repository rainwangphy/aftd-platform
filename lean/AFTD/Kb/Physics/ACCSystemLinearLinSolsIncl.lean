import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup

/-!
# ACCSystemLinear.linSolsIncl

Topic: quantum_field_theory   Node: 96e5b832b4ac

Provenance: formalization of a published result. Source: Physlib, `ACCSystemLinear.linSolsIncl`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inclusion of `LinSols` into `charges`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The inclusion of `LinSols` into `charges`. -/
def ACCSystemLinear.linSolsIncl (χ : ACCSystemLinear) : χ.LinSols →ₗ[ℚ] χ.Charges where
  toFun S := S.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
