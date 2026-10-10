import AFTD.Prelude
import AFTD.Kb.Physics.EuclideanGroup
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.EuclideanGroupInstGroup
import AFTD.Kb.Physics.EuclideanGroupInstMulActionSpace
import AFTD.Kb.Physics.SpaceInstVSubEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstZero
import AFTD.Kb.Physics.SpaceInstVAddEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceVaddApply
import AFTD.Kb.Physics.SpaceZeroApply
import AFTD.Kb.Physics.SpaceValEqIff
import AFTD.Kb.Physics.SpaceVaddVal
import AFTD.Kb.Physics.SpaceVsubApply
import AFTD.Kb.Physics.SpaceZeroVal
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
import AFTD.Kb.Physics.SpaceInstCoeFunForallFinReal
import AFTD.Kb.Physics.SpaceInstNonempty
import AFTD.Kb.Physics.SpaceInstSubsingletonOfNatNat
import AFTD.Kb.Physics.SpaceInstAddActionEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstAddTorsorEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstDist
import AFTD.Kb.Physics.SpaceInstPseudoMetricSpace
import AFTD.Kb.Physics.SpaceInstNormedAddTorsorEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstMetricSpace
import AFTD.Kb.Physics.SpaceInstNontrivial
import AFTD.Kb.Physics.SpaceInstChartedSpaceEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstIsManifoldRealEuclideanSpaceFinModelWithCornersSelfTopWithTopENat
import AFTD.Kb.Physics.SpaceSmulApply

/-!
# EuclideanGroup.smul_apply

Topic: classical_mechanics   Node: 5bfc490d1de9

Provenance: formalization of a published result. Source: Physlib, `EuclideanGroup.smul_apply`. Lean proof by Shaopeng Zhu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/EuclideanGroup/Action.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Coordinate formula for the action: `(g • p) i = (Q • (p -ᵥ origin)) i + t i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EuclideanGroup in
variable {d : ℕ} in
/-- Coordinate formula for the action: `(g • p) i = (Q • (p -ᵥ origin)) i + t i`. -/
@[simp] lemma EuclideanGroup.smul_apply (g : EuclideanGroup d) (p : Space d) (i : Fin d) :
    (g • p) i = (g.linear • (p -ᵥ (0 : Space d))) i + g.translation i := by
  show ((g.linear • (p -ᵥ (0 : Space d)) + g.translation) +ᵥ (0 : Space d)) i
    = (g.linear • (p -ᵥ (0 : Space d))) i + g.translation i
  simp [Space.vadd_apply]
