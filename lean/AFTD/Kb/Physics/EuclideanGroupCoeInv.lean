import AFTD.Prelude

/-!
# EuclideanGroup.coe_inv

Topic: classical_mechanics   Node: cab2fafc2cf5

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.coe_inv`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EuclideanGroup.coe_inv
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma EuclideanGroup.coe_inv {n : ℕ} (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    (Q⁻¹).val = (Q.val)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one]
