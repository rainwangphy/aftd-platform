import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupRotationGroup
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.EuclideanGroupInstMulActionSpace
import AFTD.Kb.Physics.SpaceInstZero
import AFTD.Kb.Physics.EuclideanGroupSpecialEuclideanGroup
import AFTD.Kb.Physics.EuclideanGroupOriginStabilizer
import AFTD.Kb.Physics.SpaceInstVAddEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstVSubEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstAddTorsorEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstAddActionEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceValEqIff
import AFTD.Kb.Physics.SpaceVaddVal
import AFTD.Kb.Physics.SpaceVaddApply
import AFTD.Kb.Physics.SpaceVsubApply
import AFTD.Kb.Physics.SpaceZeroVal
import AFTD.Kb.Physics.SpaceZeroApply
import AFTD.Kb.Physics.SpaceVectorToSpaceApply
import AFTD.Kb.Physics.SpaceVectorToSpaceVsubZero
import AFTD.Kb.Physics.SpaceChartEuclideanApply
import AFTD.Kb.Physics.EuclideanGroupOneTranslation
import AFTD.Kb.Physics.EuclideanGroupOneLinear
import AFTD.Kb.Physics.EuclideanGroupMulTranslation
import AFTD.Kb.Physics.EuclideanGroupMulLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationTranslation
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationLinear
import AFTD.Kb.Physics.EuclideanGroupOfRotationTranslationDecompose
import AFTD.Kb.Physics.EuclideanGroupOrthogonalToLinearIsometryEquivApply
import AFTD.Kb.Physics.EuclideanGroupToAffineIsometryHomApply
import AFTD.Kb.Physics.EuclideanGroupOrthogonalToLinearIsometryEquivLeftInv
import AFTD.Kb.Physics.EuclideanGroupLinearIsometryEquivConstVAddMul
import AFTD.Kb.Physics.EuclideanGroupOrthogonalToLinearIsometryEquivRightInv
import AFTD.Kb.Physics.EuclideanGroupToAffineIsometryMulEquivApply
import AFTD.Kb.Physics.EuclideanGroupSmulApply
import AFTD.Kb.Physics.EuclideanGroupSmulVsubSmul
import AFTD.Kb.Physics.EuclideanGroupRotationSmulEq
import AFTD.Kb.Physics.SpaceInstCoeFunForallFinReal
import AFTD.Kb.Physics.SpaceInstNonempty
import AFTD.Kb.Physics.SpaceInstSubsingletonOfNatNat
import AFTD.Kb.Physics.SpaceInstDist
import AFTD.Kb.Physics.SpaceInstPseudoMetricSpace
import AFTD.Kb.Physics.SpaceInstNormedAddTorsorEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstMetricSpace
import AFTD.Kb.Physics.SpaceInstNontrivial
import AFTD.Kb.Physics.SpaceInstChartedSpaceEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstIsManifoldRealEuclideanSpaceFinModelWithCornersSelfTopWithTopENat

/-!
# EuclideanGroup.rotation_smul_origin

Topic: classical_mechanics   Node: d08d9f48dcb3

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.rotation_smul_origin`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Action.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A rotation fixes the origin: its translation part vanishes (`RotationGroup ≤ OriginStabilizer`), so `↑r • 0 = 0`. Stated in the `↑r` form (the simp normal form of `r • _`, via `rotation_smul_eq`) so it is a well-formed `simp` lemma.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {d : ℕ} in
/-- A rotation fixes the origin: its translation part vanishes (`RotationGroup ≤ OriginStabilizer`), so `↑r • 0 = 0`. Stated in the `↑r` form (the simp normal form of `r • _`, via `rotation_smul_eq`) so it is a well-formed `simp` lemma. -/
@[simp] lemma EuclideanGroup.rotation_smul_origin (r : RotationGroup d) :
    (r : EuclideanGroup d) • (0 : Space d) = (0 : Space d) := by
  have h_trans : (r : EuclideanGroup d).translation = 0 := by
    apply r.property.right
  have h_rot : (r : EuclideanGroup d) • ((0 : Space d)) =
      ((r : EuclideanGroup d).linear • (0 : EuclideanSpace ℝ (Fin d)) + 0) +ᵥ ((0 : Space d)) := by
    show ((r : EuclideanGroup d).linear • ((0 : Space d) -ᵥ (0 : Space d))
        + (r : EuclideanGroup d).translation) +ᵥ (0 : Space d) = _
    rw [vsub_self, h_trans]
  simp [h_rot]
