import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.HomogeneousQuadratic
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.HomogeneousQuadraticInstFun
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup

/-!
# ACCSystemQuad.QuadSols

Topic: quantum_field_theory   Node: 3478ee237761

Provenance: formalization of a published result. Source: Physlib, `ACCSystemQuad.QuadSols`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type of solutions to the linear and quadratic ACCs.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The type of solutions to the linear and quadratic ACCs. -/
structure ACCSystemQuad.QuadSols (χ : ACCSystemQuad) extends χ.LinSols where
  /-- The condition that the charge satisfies the quadratic ACCs. -/
  quadSol : ∀ i : Fin χ.numberQuadratic, (χ.quadraticACCs i) val = 0
