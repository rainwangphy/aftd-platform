import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemSolsIncl
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction

/-!
# ACCSystem.Hom

Topic: quantum_field_theory   Node: 9803c78dc5a1

Provenance: formalization of a published result. Source: Physlib, `ACCSystem.Hom`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The structure of a map between two ACCSystems.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The structure of a map between two ACCSystems. -/
structure ACCSystem.Hom (χ η : ACCSystem) where
  /-- The linear map between vector spaces of charges. -/
  charges : χ.Charges →ₗ[ℚ] η.Charges
  /-- The map between solutions. -/
  anomalyFree : χ.Sols → η.Sols
  /-- The condition that the map commutes with the relevant inclusions. -/
  commute : charges ∘ χ.solsIncl = η.solsIncl ∘ anomalyFree
