import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsIncl
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsInclLinSolsInjective
import AFTD.Kb.Physics.ACCSystemLinearLinSolsInclInjective
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsInclLinSols
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# ACCSystemQuad.quadSolsIncl_injective

Topic: quantum_field_theory   Node: 042cd814fbb3

Provenance: formalization of a published result. Source: Physlib, `ACCSystemQuad.quadSolsIncl_injective`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ACCSystemQuad.quadSolsIncl_injective
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma ACCSystemQuad.quadSolsIncl_injective (χ : ACCSystemQuad) :
    Function.Injective χ.quadSolsIncl :=
  fun _ _ h => quadSolsInclLinSols_injective χ
    (ACCSystemLinear.linSolsIncl_injective χ.toACCSystemLinear h)
