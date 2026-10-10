import AFTD.Prelude

/-!
# EuclideanGroup.linearIsometryEquiv_constVAdd_mul

Topic: classical_mechanics   Node: a14eb1bc6871

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.linearIsometryEquiv_constVAdd_mul`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/AffineGroup.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The affine map `x ↦ t +ᵥ L x`, projected to its linear isometry component, is `L`. Together with `orthogonalToLinearIsometryEquiv_left_inv`, this proves `left_inv` of `toAffineIsometryMulEquiv`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {n : ℕ} in
/-- The affine map `x ↦ t +ᵥ L x`, projected to its linear isometry component, is `L`. Together with `orthogonalToLinearIsometryEquiv_left_inv`, this proves `left_inv` of `toAffineIsometryMulEquiv`. -/
@[simp] lemma EuclideanGroup.linearIsometryEquiv_constVAdd_mul
    (t : EuclideanSpace ℝ (Fin n))
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    ((AffineIsometryEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin n)) t *
        L.toAffineIsometryEquiv).linearIsometryEquiv) = L := by
  apply LinearIsometryEquiv.ext; intro x
  have h := (AffineIsometryEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin n)) t *
      L.toAffineIsometryEquiv).map_vsub x 0
  rw [vsub_eq_sub, sub_zero] at h
  rw [h]
  simp
