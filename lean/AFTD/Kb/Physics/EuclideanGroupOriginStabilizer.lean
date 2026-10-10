import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear

/-!
# EuclideanGroup.OriginStabilizer

Topic: classical_mechanics   Node: f3d6509aadc0

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.OriginStabilizer`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The subgroup of `EuclideanGroup n` whose elements fix the origin (translation = 0). This is the copy of `O(n)` sitting inside `E(n)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The subgroup of `EuclideanGroup n` whose elements fix the origin (translation = 0). This is the copy of `O(n)` sitting inside `E(n)`. -/
def EuclideanGroup.OriginStabilizer (n : ℕ) : Subgroup (EuclideanGroup n) where
  carrier := {g | g.translation = 0}
  mul_mem' {a b} ha hb := by
    show a.translation + a.linear • b.translation = 0
    rw [ha, hb, smul_zero, zero_add]
  one_mem' := rfl
  inv_mem' {a} ha := by
    show a.linear⁻¹ • (-a.translation) = 0
    rw [ha, neg_zero, smul_zero]
