import AFTD.Prelude
import AFTD.Kb.Physics.GroupTheorySO3

/-!
# GroupTheory.SO3Group

Topic: classical_mechanics   Node: e18f4cfc2fca

Provenance: formalization of a published result. Source: Physlib, `GroupTheory.SO3Group`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Groups/SO3/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The instance of a group on `SO3`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
/-- The instance of a group on `SO3`. -/
@[simps! mul_coe one_coe inv div]
instance GroupTheory.SO3Group : Group SO3 where
  mul A B := ⟨A.1 * B.1,
    by
      simp only [det_mul, A.2.1, B.2.1, mul_one],
    by
      simp only [transpose_mul, Matrix.mul_assoc]
      trans A.1 * ((B.1 * (B.1)ᵀ) * (A.1)ᵀ)
      · noncomm_ring
      · simp [B.2.2, A.2.2]⟩
  mul_assoc A B C := Subtype.ext (Matrix.mul_assoc A.1 B.1 C.1)
  one := ⟨1, det_one, by rw [transpose_one, mul_one]⟩
  one_mul A := Subtype.ext (Matrix.one_mul A.1)
  mul_one A := Subtype.ext (Matrix.mul_one A.1)
  inv A := ⟨A.1ᵀ, by simp only [det_transpose, A.2],
    by simp only [transpose_transpose, mul_eq_one_comm.mpr A.2.2]⟩
  inv_mul_cancel A := Subtype.ext (mul_eq_one_comm.mpr A.2.2)
