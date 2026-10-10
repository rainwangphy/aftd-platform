import AFTD.Prelude
import AFTD.Kb.Physics.TimeMan
import AFTD.Kb.Physics.TimeManInstTopologicalSpace
import AFTD.Kb.Physics.TimeManIsOpenIff
import AFTD.Kb.Physics.TimeManValRange
import AFTD.Kb.Physics.Time

/-!
# TimeMan.valHomeomorphism

Topic: classical_mechanics   Node: 21427aaabf16

Provenance: formalization of a published result. Source: Physlib, `TimeMan.valHomeomorphism`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Time/TimeMan.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The choice of map `Time.val` from `TimeMan` to `ℝ` as a homeomorphism.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The choice of map `Time.val` from `TimeMan` to `ℝ` as a homeomorphism. -/
def TimeMan.valHomeomorphism : TimeMan ≃ₜ ℝ where
  toFun := TimeMan.val
  invFun := fun t => { val := t }
  left_inv := by
    intro t
    cases t
    rfl
  right_inv := by
    intro t
    rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    refine { isOpen_preimage := ?_ }
    intro s hs
    rw [isOpen_iff] at hs
    rw [← Set.image_eq_preimage_of_inverse]
    · exact hs
    · intro t
      rfl
    · intro x
      simp
