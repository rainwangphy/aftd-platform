import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemCharges

/-!
# ACCSystemCharges.Charges

Topic: quantum_field_theory   Node: c70042c5102b

Provenance: formalization of a published result. Source: Physlib, `ACCSystemCharges.Charges`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The charges as functions from `Fin χ.numberCharges → ℚ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The charges as functions from `Fin χ.numberCharges → ℚ`. -/
def ACCSystemCharges.Charges (χ : ACCSystemCharges) : Type := Fin χ.numberCharges → ℚ
