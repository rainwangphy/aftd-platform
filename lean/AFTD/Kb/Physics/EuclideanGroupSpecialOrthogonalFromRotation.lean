import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupRotationGroup
import AFTD.Kb.Physics.EuclideanGroupRotationsAboutToOrigin
import AFTD.Kb.Physics.EuclideanGroupSpecialEuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupOriginStabilizer
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationTranslation
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationDecompose

/-!
# EuclideanGroup.specialOrthogonal.fromRotation

Topic: classical_mechanics   Node: 64caf164cfcf

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.specialOrthogonal.fromRotation`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The isomorphism's inverse map: the linear part of a rotation about the origin, as a special orthogonal matrix.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n} (p : EuclideanSpace ℝ (Fin n)) in
/-- The isomorphism's inverse map: the linear part of a rotation about the origin, as a special orthogonal matrix. -/
noncomputable def EuclideanGroup.specialOrthogonal.fromRotation (n : ℕ) :
    RotationGroup n →* Matrix.specialOrthogonalGroup (Fin n) ℝ where
  toFun g := ⟨g.val.linear, ⟨g.val.linear.property,(g.property).left⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl
