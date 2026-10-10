import AFTD.Prelude

/-!
# AffineIsometryEquiv.toAffineEquivHom

Topic: classical_mechanics   Node: 4ed2c324b3e5

Provenance: formalization of a published result. Source: Physlib, `AffineIsometryEquiv.toAffineEquivHom`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/AffineGroup.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The second leg of the inclusion: `AffineIsometryEquiv.toAffineEquiv` bundled as a monoid homomorphism into the affine automorphism group.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {n : ℕ} in
/-- The second leg of the inclusion: `AffineIsometryEquiv.toAffineEquiv` bundled as a monoid homomorphism into the affine automorphism group. -/
noncomputable def AffineIsometryEquiv.toAffineEquivHom :
    AffineIsometryEquiv ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) →*
      AffineEquiv ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) where
  toFun e := e.toAffineEquiv
  map_one' := by
    apply AffineEquiv.ext; intro x; trivial
  map_mul' e e' := by
    apply AffineEquiv.ext; intro x; simp
