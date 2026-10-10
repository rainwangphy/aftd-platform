import AFTD.Prelude

/-!
# EuclideanGroup.linearIsometryEquivToOrthogonal

Topic: classical_mechanics   Node: f3d01fe357aa

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.linearIsometryEquivToOrthogonal`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/AffineGroup.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `invFun` ingredient of `toAffineIsometryMulEquiv`: a linear isometry equivalence read back as an orthogonal matrix, inverse to the linear bridge `orthogonalToLinearIsometryEquiv` (see the round-trip `@[simp]` lemmas below).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {n : ℕ} in
/-- The `invFun` ingredient of `toAffineIsometryMulEquiv`: a linear isometry equivalence read back as an orthogonal matrix, inverse to the linear bridge `orthogonalToLinearIsometryEquiv` (see the round-trip `@[simp]` lemmas below). -/
noncomputable def EuclideanGroup.linearIsometryEquivToOrthogonal
    (L : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)) :
    Matrix.orthogonalGroup (Fin n) ℝ :=
   let b := EuclideanSpace.basisFun (Fin n) ℝ
   ⟨LinearMap.toMatrix b.toBasis b.toBasis L.toLinearEquiv, by
    have hb : LinearMap.toMatrix b.toBasis b.toBasis L.toLinearEquiv
        = b.toBasis.toMatrix (b.map L) := by
      ext i j
      simp [LinearMap.toMatrix_apply, Module.Basis.toMatrix_apply,
        OrthonormalBasis.map_apply, OrthonormalBasis.coe_toBasis_repr_apply]
    rw [hb]
    exact b.toMatrix_orthonormalBasis_mem_orthogonal (b.map L)⟩
