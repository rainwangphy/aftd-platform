import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemLinearLinSolsIncl
import AFTD.Kb.Physics.ACCSystemLinearLinSolsExt
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup

/-!
# ACCSystemLinear.linSolsIncl_injective

Topic: quantum_field_theory   Node: 95ca75fd6ce0

Provenance: formalization of a published result. Source: Physlib, `ACCSystemLinear.linSolsIncl_injective`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ACCSystemLinear.linSolsIncl_injective
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma ACCSystemLinear.linSolsIncl_injective (χ : ACCSystemLinear) :
    Function.Injective χ.linSolsIncl := fun _ _ h => LinSols.ext h
