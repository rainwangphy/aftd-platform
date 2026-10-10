import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.AffineIsometryEquivToAffineEquivHom
import AFTD.Kb.Physics.EuclideanGroupToAffineIsometryHom
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationTranslation
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationDecompose
import AFTD.Kb.Physics.EuclideanGroupOrthogonalToLinearIsometryEquivApply
import AFTD.Kb.Physics.EuclideanGroupToAffineIsometryHomApply

/-!
# EuclideanGroup.toAffineEquiv

Topic: classical_mechanics   Node: f794005cfbf9

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.toAffineEquiv`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/AffineGroup.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inclusion of the Euclidean group into Mathlib's affine automorphism group: the composite of the two legs `toAffineIsometryHom` and `AffineIsometryEquiv.toAffineEquivHom`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n : ℕ} in
/-- The inclusion of the Euclidean group into Mathlib's affine automorphism group: the composite of the two legs `toAffineIsometryHom` and `AffineIsometryEquiv.toAffineEquivHom`. -/
noncomputable def EuclideanGroup.toAffineEquiv :
    EuclideanGroup n →* AffineEquiv ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  AffineIsometryEquiv.toAffineEquivHom.comp toAffineIsometryHom
