import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule

/-!
# ACCSystemCharges.ChargesAddCommGroup

Topic: quantum_field_theory   Node: 744cd0e8f6ea

Provenance: formalization of a published result. Source: Physlib, `ACCSystemCharges.ChargesAddCommGroup`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ACCSystemCharges.ChargesAddCommGroup
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance ACCSystemCharges.ChargesAddCommGroup (χ : ACCSystemCharges) : AddCommGroup χ.Charges :=
  Module.addCommMonoidToAddCommGroup ℚ
