import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystem
import AFTD.Kb.Physics.ACCSystemSols
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystemSolsMulAction
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemSolsIncl
import AFTD.Kb.Physics.ACCSystemSolsInclQuadSolsInjective
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsInclInjective
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemSolsInclQuadSols
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup

/-!
# ACCSystem.solsIncl_injective

Topic: quantum_field_theory   Node: 1792682e49b4

Provenance: formalization of a published result. Source: Physlib, `ACCSystem.solsIncl_injective`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ACCSystem.solsIncl_injective
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma ACCSystem.solsIncl_injective (χ : ACCSystem) :
    Function.Injective χ.solsIncl :=
  fun _ _ h => solsInclQuadSols_injective χ
    (ACCSystemQuad.quadSolsIncl_injective χ.toACCSystemQuad h)
