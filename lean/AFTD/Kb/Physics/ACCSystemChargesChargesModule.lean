import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid

/-!
# ACCSystemCharges.chargesModule

Topic: quantum_field_theory   Node: 34ea7021530e

Provenance: formalization of a published result. Source: Physlib, `ACCSystemCharges.chargesModule`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An instance to provide the necessary operations and properties for `charges` to form a module over the field `ℚ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An instance to provide the necessary operations and properties for `charges` to form a module over the field `ℚ`. -/
@[simps!]
instance ACCSystemCharges.chargesModule (χ : ACCSystemCharges) : Module ℚ χ.Charges :=
  Pi.module _ _ _
