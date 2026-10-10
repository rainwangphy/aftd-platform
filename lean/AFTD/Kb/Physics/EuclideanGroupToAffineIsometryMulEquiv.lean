import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupLinearIsometryEquivToOrthogonal
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupToAffineIsometryHom
import AFTD.Kb.Physics.EuclideanGroupOrthogonalToLinearIsometryEquiv
import AFTD.Kb.Physics.EuclideanGroupLinearIsometryEquivConstVAddMul
import AFTD.Kb.Physics.EuclideanGroupOrthogonalToLinearIsometryEquivLeftInv
import AFTD.Kb.Physics.EuclideanGroupOrthogonalToLinearIsometryEquivRightInv
import AFTD.Kb.Physics.EuclideanGroupToAffineIsometryHomApply
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationTranslation
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationDecompose
import AFTD.Kb.Physics.EuclideanGroupOrthogonalToLinearIsometryEquivApply

/-!
# EuclideanGroup.toAffineIsometryMulEquiv

Topic: classical_mechanics   Node: 925c6a8b1914

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.toAffineIsometryMulEquiv`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/AffineGroup.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`EuclideanGroup n ≃* AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin n)) _`: the Euclidean group is the full group of affine isometries of Euclidean space. This upgrades `toAffineIsometryHom` to a group isomorphism with the same underlying map.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n : ℕ} in
/-- `EuclideanGroup n ≃* AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin n)) _`: the Euclidean group is the full group of affine isometries of Euclidean space. This upgrades `toAffineIsometryHom` to a group isomorphism with the same underlying map. -/
noncomputable def EuclideanGroup.toAffineIsometryMulEquiv :
    EuclideanGroup n ≃*
      AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) where
  toFun := toAffineIsometryHom
  invFun e := ⟨e 0, linearIsometryEquivToOrthogonal e.linearIsometryEquiv⟩
  left_inv A := by
    refine EuclideanGroup.ext ?_ ?_
    · simp
    · simp [linearIsometryEquiv_constVAdd_mul, orthogonalToLinearIsometryEquiv_left_inv]
  right_inv e := by
    apply AffineIsometryEquiv.ext; intro x
    simp only [toAffineIsometryHom_apply,
      orthogonalToLinearIsometryEquiv_right_inv,
      AffineIsometryEquiv.coe_mul, Function.comp_apply,
      LinearIsometryEquiv.coe_toAffineIsometryEquiv,
      AffineIsometryEquiv.coe_constVAdd, vadd_eq_add]
    have h := e.map_vadd 0 x
    simp [vadd_eq_add, add_zero] at h
    rw [h, add_comm]
  map_mul' := toAffineIsometryHom.map_mul'
