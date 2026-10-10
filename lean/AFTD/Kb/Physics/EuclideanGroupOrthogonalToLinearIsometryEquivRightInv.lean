import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroupOrthogonalToLinearIsometryEquiv
import AFTD.Kb.Physics.EuclideanGroupLinearIsometryEquivToOrthogonal
import AFTD.Kb.Physics.EuclideanGroupOrthogonalToLinearIsometryEquivApply
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationTranslation
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationDecompose
import AFTD.Kb.Physics.EuclideanGroupToAffineIsometryHomApply
import AFTD.Kb.Physics.EuclideanGroupOrthogonalToLinearIsometryEquivLeftInv
import AFTD.Kb.Physics.EuclideanGroupLinearIsometryEquivConstVAddMul
import AFTD.Kb.Physics.EuclideanGroupInstGroup

/-!
# EuclideanGroup.orthogonalToLinearIsometryEquiv_right_inv

Topic: classical_mechanics   Node: a90a50abaa2d

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.orthogonalToLinearIsometryEquiv_right_inv`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/AffineGroup.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`linearIsometryEquivToOrthogonal` is a right inverse of `orthogonalToLinearIsometryEquiv`; this proves `right_inv` of `toAffineIsometryMulEquiv`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n : ℕ} in
/-- `linearIsometryEquivToOrthogonal` is a right inverse of `orthogonalToLinearIsometryEquiv`; this proves `right_inv` of `toAffineIsometryMulEquiv`. -/
@[simp] lemma EuclideanGroup.orthogonalToLinearIsometryEquiv_right_inv
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    orthogonalToLinearIsometryEquiv (linearIsometryEquivToOrthogonal L) = L := by
    apply LinearIsometryEquiv.ext; intro x
    rw [orthogonalToLinearIsometryEquiv_apply]
    show Matrix.toEuclideanLin (linearIsometryEquivToOrthogonal L).val x = L x
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
    show Matrix.toLin _ _
        (LinearMap.toMatrix _ _
          (L.toLinearEquiv : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))) x = L x
    rw [Matrix.toLin_toMatrix]
    rfl
