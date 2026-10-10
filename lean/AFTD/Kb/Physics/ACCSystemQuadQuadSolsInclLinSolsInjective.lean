import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemQuad
import AFTD.Kb.Physics.ACCSystemQuadQuadSols
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsMulAction
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommGroup
import AFTD.Kb.Physics.ACCSystemLinearLinSolsAddCommMonoid
import AFTD.Kb.Physics.ACCSystemLinearLinSolsModule
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsInclLinSols
import AFTD.Kb.Physics.ACCSystemQuadQuadSolsExt
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# ACCSystemQuad.quadSolsInclLinSols_injective

Topic: quantum_field_theory   Node: 0e7ed2f0cdb2

Provenance: formalization of a published result. Source: Physlib, `ACCSystemQuad.quadSolsInclLinSols_injective`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ACCSystemQuad.quadSolsInclLinSols_injective
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma ACCSystemQuad.quadSolsInclLinSols_injective (χ : ACCSystemQuad) :
    Function.Injective χ.quadSolsInclLinSols :=
  fun _ _ h => QuadSols.ext (congrArg (fun X => X.val) h)
