import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup

/-!
# ACCSystemCharges.instFiniteRatCharges

Topic: quantum_field_theory   Node: 77b290d45b95

Provenance: formalization of a published result. Source: Physlib, `ACCSystemCharges.instFiniteRatCharges`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The module `χ.Charges` over `ℚ` is finite.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The module `χ.Charges` over `ℚ` is finite. -/
instance ACCSystemCharges.instFiniteRatCharges (χ : ACCSystemCharges) : Module.Finite ℚ χ.Charges :=
  FiniteDimensional.finiteDimensional_pi ℚ
