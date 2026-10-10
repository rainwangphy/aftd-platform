import AFTD.Prelude
import AFTD.Kb.Physics.ACCSystemChargesCharges
import AFTD.Kb.Physics.MSSMCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommMonoid
import AFTD.Kb.Physics.ACCSystemCharges
import AFTD.Kb.Physics.ACCSystemChargesChargesModule
import AFTD.Kb.Physics.ACCSystemChargesChargesAddCommGroup
import AFTD.Kb.Physics.ACCSystemChargesInstFiniteRatCharges

/-!
# MSSMCharges.Hd

Topic: quantum_field_theory   Node: 60e9d96edb47

Provenance: formalization of a published result. Source: Physlib, `MSSMCharges.Hd`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/MSSMNu/AnomalyCancellation/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The charge `Hd`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
open BigOperators in
/-- The charge `Hd`. -/
@[simps!]
def MSSMCharges.Hd : MSSMCharges.Charges →ₗ[ℚ] ℚ where
  toFun S := S ⟨18, Nat.lt_of_sub_eq_succ rfl⟩
  map_add' _ _ := by rfl
  map_smul' _ _ := by rfl
