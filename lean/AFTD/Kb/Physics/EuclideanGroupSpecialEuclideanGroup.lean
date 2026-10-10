import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupDetCoeInv
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear

/-!
# EuclideanGroup.SpecialEuclideanGroup

Topic: classical_mechanics   Node: 7eecfbf842a8

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.SpecialEuclideanGroup`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Special Euclidean Group is the subgroup with det(Q) = 1 where Q ∈ O(n)
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Special Euclidean Group is the subgroup with det(Q) = 1 where Q ∈ O(n) -/
def EuclideanGroup.SpecialEuclideanGroup (n : ℕ) : Subgroup (EuclideanGroup n) where
  carrier := {g | g.linear.val.det = 1}
  mul_mem' {a b} ha hb := by
    show (a.linear * b.linear).val.det = 1
    rw [Submonoid.coe_mul, Matrix.det_mul, ha, hb, one_mul]
  one_mem' := by
    show (1 : ↥(Matrix.orthogonalGroup (Fin n) ℝ)).val.det = 1
    rw [OneMemClass.coe_one, Matrix.det_one]
  inv_mem' {a} ha := by
    show (a.linear⁻¹).val.det = 1
    rw [det_coe_inv, ha, inv_one]
