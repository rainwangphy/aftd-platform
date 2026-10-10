import AFTD.Prelude

/-!
# EuclideanGroup.det_coe_inv

Topic: classical_mechanics   Node: dc7200c80cdb

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.det_coe_inv`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EuclideanGroup.det_coe_inv
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma EuclideanGroup.det_coe_inv {n : ℕ} (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    (Q⁻¹).val.det = (Q.val.det)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← Matrix.det_mul, ← Submonoid.coe_mul, mul_inv_cancel,
    OneMemClass.coe_one, Matrix.det_one]
