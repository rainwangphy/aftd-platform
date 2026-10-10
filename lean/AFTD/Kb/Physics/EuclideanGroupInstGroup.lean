import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup

/-!
# EuclideanGroup.instGroup

Topic: classical_mechanics   Node: 3b409b35a32d

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.instGroup`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Group structure on `E(n) = ℝ^n ⋊ O(n)`. The orthogonal component acts on translations by the inherited matrix-vector action on `EuclideanSpace ℝ (Fin n)`, transported through `WithLp` from the coordinate action `Q.val *ᵥ v.ofLp`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Group structure on `E(n) = ℝ^n ⋊ O(n)`. The orthogonal component acts on translations by the inherited matrix-vector action on `EuclideanSpace ℝ (Fin n)`, transported through `WithLp` from the coordinate action `Q.val *ᵥ v.ofLp`. -/
noncomputable instance EuclideanGroup.instGroup : Group (EuclideanGroup n) where
  mul A B := ⟨A.translation + A.linear • B.translation, A.linear * B.linear⟩
  mul_assoc A B C := by
    refine EuclideanGroup.ext ?_ ?_
    · show A.translation + A.linear • B.translation + (A.linear * B.linear) • C.translation
        = A.translation + A.linear • (B.translation + B.linear • C.translation)
      rw [mul_smul, smul_add, add_assoc]
    · exact mul_assoc A.linear B.linear C.linear
  one := ⟨0, 1⟩
  one_mul A := by
    refine EuclideanGroup.ext ?_ ?_
    · show 0 + (1 : Matrix.orthogonalGroup (Fin n) ℝ) • A.translation = A.translation
      rw [zero_add, one_smul]
    · exact one_mul A.linear
  mul_one A := by
    refine EuclideanGroup.ext ?_ ?_
    · show A.translation + A.linear • 0 = A.translation
      rw [smul_zero, add_zero]
    · exact mul_one A.linear
  inv A := ⟨A.linear⁻¹ • (-A.translation), A.linear⁻¹⟩
  inv_mul_cancel A := by
    refine EuclideanGroup.ext ?_ ?_
    · show A.linear⁻¹ • (-A.translation) + A.linear⁻¹ • A.translation = 0
      rw [← smul_add, neg_add_cancel, smul_zero]
    · exact inv_mul_cancel A.linear
