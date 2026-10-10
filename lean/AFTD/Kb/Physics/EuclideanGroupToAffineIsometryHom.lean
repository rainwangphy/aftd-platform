import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupOrthogonalToLinearIsometryEquiv
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationTranslation
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationDecompose
import AFTD.Kb.Physics.EuclideanGroupOrthogonalToLinearIsometryEquivApply

/-!
# EuclideanGroup.toAffineIsometryHom

Topic: classical_mechanics   Node: 08684f9fc064

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.toAffineIsometryHom`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/AffineGroup.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The first leg of the inclusion: `⟨t, Q⟩ ↦ (x ↦ Q x + t)`, bundled as a monoid homomorphism from the Euclidean group into the affine isometry group of `EuclideanSpace ℝ (Fin n)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n : ℕ} in
/-- The first leg of the inclusion: `⟨t, Q⟩ ↦ (x ↦ Q x + t)`, bundled as a monoid homomorphism from the Euclidean group into the affine isometry group of `EuclideanSpace ℝ (Fin n)`. -/
noncomputable def EuclideanGroup.toAffineIsometryHom :
    EuclideanGroup n →*
      AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) where
  toFun A := AffineIsometryEquiv.constVAdd ℝ (EuclideanSpace ℝ (Fin n)) A.translation *
    (orthogonalToLinearIsometryEquiv A.linear).toAffineIsometryEquiv
  map_one' := by
    apply AffineIsometryEquiv.ext
    intro x; simp
  map_mul' A B := by
    apply AffineIsometryEquiv.ext
    intro x
    simp [mul_smul, add_assoc]
