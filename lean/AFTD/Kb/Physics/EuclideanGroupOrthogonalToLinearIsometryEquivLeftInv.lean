import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroupLinearIsometryEquivToOrthogonal
import AFTD.Kb.Physics.EuclideanGroupOrthogonalToLinearIsometryEquiv
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationTranslation
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationDecompose
import AFTD.Kb.Physics.EuclideanGroupOrthogonalToLinearIsometryEquivApply
import AFTD.Kb.Physics.EuclideanGroupToAffineIsometryHomApply
import AFTD.Kb.Physics.EuclideanGroupInstGroup

/-!
# EuclideanGroup.orthogonalToLinearIsometryEquiv_left_inv

Topic: classical_mechanics   Node: 99d121a91f63

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.orthogonalToLinearIsometryEquiv_left_inv`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/AffineGroup.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`linearIsometryEquivToOrthogonal` is a left inverse of `orthogonalToLinearIsometryEquiv`. Together with `linearIsometryEquiv_constVAdd_mul`, this proves `left_inv` of `toAffineIsometryMulEquiv`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n : ℕ} in
/-- `linearIsometryEquivToOrthogonal` is a left inverse of `orthogonalToLinearIsometryEquiv`. Together with `linearIsometryEquiv_constVAdd_mul`, this proves `left_inv` of `toAffineIsometryMulEquiv`. -/
@[simp] lemma EuclideanGroup.orthogonalToLinearIsometryEquiv_left_inv
    (Q : Matrix.orthogonalGroup (Fin n) ℝ) :
    linearIsometryEquivToOrthogonal (orthogonalToLinearIsometryEquiv Q) = Q := by
  apply Subtype.ext
  have hlin :
      ((orthogonalToLinearIsometryEquiv Q).toLinearEquiv :
          EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
        = Matrix.toLin (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin n) ℝ).toBasis Q.val := by
    ext x; rfl
  show LinearMap.toMatrix _ _
      ((orthogonalToLinearIsometryEquiv Q).toLinearEquiv :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) = Q.val
  rw [hlin, LinearMap.toMatrix_toLin]
