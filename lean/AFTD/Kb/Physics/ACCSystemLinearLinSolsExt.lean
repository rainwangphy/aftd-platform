import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemLinear
import AFTD.Kb.Physics.ACCSystemLinearLinSols
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# ACCSystemLinear.LinSols.ext

Topic: quantum_field_theory   Node: acddcb75e4fa

Provenance: formalization of a published result. Source: Physlib, `ACCSystemLinear.LinSols.ext`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Two solutions are equal if the underlying charges are equal.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Two solutions are equal if the underlying charges are equal. -/
@[ext]
lemma ACCSystemLinear.LinSols.ext {χ : ACCSystemLinear} {S T : χ.LinSols} (h : S.val = T.val) : S = T := by
  cases' S
  simp_all only
