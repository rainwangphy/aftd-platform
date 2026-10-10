import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupRotationGroup
import AFTD.Kb.Physics.EuclideanGroupRotationsAboutToOrigin
import AFTD.Kb.Physics.EuclideanGroupOfRotation
import AFTD.Kb.Physics.EuclideanGroupSpecialEuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupOriginStabilizer
import AFTD.Kb.Physics.EuclideanGroupSpecialOrthogonalIncl
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationTranslation
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationDecompose

/-!
# EuclideanGroup.specialOrthogonal.toRotation

Topic: classical_mechanics   Node: 6bc843b01ba8

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.specialOrthogonal.toRotation`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Basic.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The isomorphism's forward map: a special orthogonal matrix as a rotation about the origin.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {n} (p : EuclideanSpace ℝ (Fin n)) in
/-- The isomorphism's forward map: a special orthogonal matrix as a rotation about the origin. -/
noncomputable def EuclideanGroup.specialOrthogonal.toRotation (n : ℕ) :
    Matrix.specialOrthogonalGroup (Fin n) ℝ →* RotationGroup n where
  toFun g := ⟨ofRotation g, by
      refine ⟨?_, ?_⟩
      · show (ofRotation g).linear.val.det = 1
        exact (Matrix.mem_specialOrthogonalGroup_iff.mp g.property).right
      · show (ofRotation g).translation = 0
        rfl⟩
  map_one' := rfl
  map_mul' x y := by
    apply Subtype.ext
    refine EuclideanGroup.ext ?_ ?_
    · show (0 : EuclideanSpace ℝ (Fin n)) =
        0 + (specialOrthogonal.incl n x : Matrix.orthogonalGroup (Fin n) ℝ) • 0
      rw [smul_zero, add_zero]
    · show specialOrthogonal.incl n (x * y)
          = specialOrthogonal.incl n x * specialOrthogonal.incl n y
      rw [map_mul]
