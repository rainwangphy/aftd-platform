import AFTD.Prelude

/-!
# EuclideanGroup.orthogonalToLinearIsometryEquiv

Topic: classical_mechanics   Node: 41abb4e844ea

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.orthogonalToLinearIsometryEquiv`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/AffineGroup.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An orthogonal matrix viewed as a linear isometry equivalence of `EuclideanSpace ℝ (Fin n)`; the linear ingredient of the first leg `toAffineIsometryHom`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {n : ℕ} in
open scoped Matrix in
/-- An orthogonal matrix viewed as a linear isometry equivalence of `EuclideanSpace ℝ (Fin n)`; the linear ingredient of the first leg `toAffineIsometryHom`. -/
noncomputable def EuclideanGroup.orthogonalToLinearIsometryEquiv
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  (DistribMulAction.toLinearEquiv ℝ (EuclideanSpace ℝ (Fin n)) Q).isometryOfInner fun x y => by
    simp only [DistribMulAction.toLinearEquiv_apply,
      EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    show (Q.val *ᵥ y.ofLp) ⬝ᵥ (Q.val *ᵥ x.ofLp) = y.ofLp ⬝ᵥ x.ofLp
    have hQ : (Q.val)ᵀ * Q.val = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp Q.property
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, hQ, Matrix.vecMul_one]
