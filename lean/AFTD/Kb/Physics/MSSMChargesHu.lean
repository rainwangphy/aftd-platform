import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# MSSMCharges.Hu

Topic: quantum_field_theory   Node: 7a5cea1754df

Provenance: formalization of a published result. Source: Physlib, `MSSMCharges.Hu`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The charge `Hu`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
/-- The charge `Hu`. -/
@[simps!]
def MSSMCharges.Hu : MSSMCharges.Charges →ₗ[ℚ] ℚ where
  toFun S := S ⟨19, Nat.lt_of_sub_eq_succ rfl⟩
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl
