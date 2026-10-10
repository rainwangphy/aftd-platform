import AFTD.Prelude

/-!
# GalileanGroup.orthogonal_smul_smul

Topic: classical_mechanics   Node: 6a23b5e0b038

Provenance: formalization of a published result. Source: Physlib, `GalileanGroup.orthogonal_smul_smul`. Lean proof by Rob Sneiderman, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/GalileanGroup/Basic.lean (Copyright (c) 2026 Rob Sneiderman. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GalileanGroup.orthogonal_smul_smul
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {d : ℕ} in
lemma GalileanGroup.orthogonal_smul_smul (R : Matrix.orthogonalGroup (Fin d) ℝ) (c : ℝ)
    (v : EuclideanSpace ℝ (Fin d)) :
    R • (c • v) = c • (R • v) := by
  change (DistribMulAction.toLinearEquiv ℝ (EuclideanSpace ℝ (Fin d)) R) (c • v) =
    c • ((DistribMulAction.toLinearEquiv ℝ (EuclideanSpace ℝ (Fin d)) R) v)
  rw [map_smul]
