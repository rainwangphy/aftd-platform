import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule

/-!
# ACCSystemLinear.linSolsAddCommGroup

Topic: quantum_field_theory   Node: 566ad951d2d7

Provenance: formalization of a published result. Source: Physlib, `ACCSystemLinear.linSolsAddCommGroup`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ACCSystemLinear.linSolsAddCommGroup
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance ACCSystemLinear.linSolsAddCommGroup (χ : ACCSystemLinear) : AddCommGroup χ.LinSols :=
  Module.addCommMonoidToAddCommGroup ℚ
