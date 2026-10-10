import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# ACCSystemLinear.LinSols

Topic: quantum_field_theory   Node: ae39ed04096b

Provenance: formalization of a published result. Source: Physlib, `ACCSystemLinear.LinSols`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type of solutions to the linear ACCs.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The type of solutions to the linear ACCs. -/
structure ACCSystemLinear.LinSols (χ : ACCSystemLinear) where
  /-- The underlying charge. -/
  val : χ.1.Charges
  /-- The condition that the charge satisfies the linear ACCs. -/
  linearSol : ∀ i : Fin χ.numberLinear, χ.linearACCs i val = 0
