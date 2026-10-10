import AFTD.Prelude
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.SpaceInstSeminormedAddCommGroup
import AFTD.Kb.Physics.SpaceInstInnerProductSpaceReal
import AFTD.Kb.Physics.SpaceValEqIff
import AFTD.Kb.Physics.SpaceVaddVal
import AFTD.Kb.Physics.SpaceVaddApply
import AFTD.Kb.Physics.SpaceVsubApply
import AFTD.Kb.Physics.SpaceZeroVal
import AFTD.Kb.Physics.SpaceZeroApply
import AFTD.Kb.Physics.SpaceVectorToSpaceApply
import AFTD.Kb.Physics.SpaceVectorToSpaceVsubZero
import AFTD.Kb.Physics.SpaceChartEuclideanApply
import AFTD.Kb.Physics.SpaceAddVal
import AFTD.Kb.Physics.SpaceAddApply
import AFTD.Kb.Physics.SpaceNsmulVal
import AFTD.Kb.Physics.SpaceNsmulApply
import AFTD.Kb.Physics.SpaceAddVaddZero
import AFTD.Kb.Physics.SpaceSmulVal
import AFTD.Kb.Physics.SpaceSmulApply
import AFTD.Kb.Physics.SpaceSmulVaddZero
import AFTD.Kb.Physics.SpaceAbsEvalLeNorm
import AFTD.Kb.Physics.SpaceNormVaddZero
import AFTD.Kb.Physics.SpaceNegVal
import AFTD.Kb.Physics.SpaceNegApply
import AFTD.Kb.Physics.SpaceSubApply
import AFTD.Kb.Physics.SpaceSubVal
import AFTD.Kb.Physics.SpaceVaddZeroSubVaddZero
import AFTD.Kb.Physics.SpaceDistEqNorm
import AFTD.Kb.Physics.SpaceInnerVaddZero
import AFTD.Kb.Physics.SpaceInstCoeFunForallFinReal
import AFTD.Kb.Physics.SpaceInstNonempty
import AFTD.Kb.Physics.SpaceInstSubsingletonOfNatNat
import AFTD.Kb.Physics.SpaceInstVAddEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstAddActionEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstVSubEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstAddTorsorEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstDist
import AFTD.Kb.Physics.SpaceInstPseudoMetricSpace
import AFTD.Kb.Physics.SpaceInstNormedAddTorsorEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstMetricSpace
import AFTD.Kb.Physics.SpaceInstNontrivial
import AFTD.Kb.Physics.SpaceInstChartedSpaceEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstIsManifoldRealEuclideanSpaceFinModelWithCornersSelfTopWithTopENat
import AFTD.Kb.Physics.SpaceInstZero
import AFTD.Kb.Physics.SpaceInstAdd
import AFTD.Kb.Physics.SpaceInstAddCommMonoid
import AFTD.Kb.Physics.SpaceInstSMulReal
import AFTD.Kb.Physics.SpaceInstModuleReal
import AFTD.Kb.Physics.SpaceInstNorm
import AFTD.Kb.Physics.SpaceInstNeg
import AFTD.Kb.Physics.SpaceInstAddCommGroup
import AFTD.Kb.Physics.SpaceInstNormedAddCommGroup
import AFTD.Kb.Physics.SpaceInstInnerReal

/-!
# Space.instNormedSpaceReal

Topic: classical_mechanics   Node: b5e63e9081a6

Provenance: formalization of a published result. Source: Physlib, `Space.instNormedSpaceReal`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Module.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The normed space structure on `Space d`, registered directly. It is definitionally the one underlying the inner product space structure, but registering it as its own instance is needed for typeclass search to find the operator-norm structure on `Space d →L[ℝ] ℝ` (for example `NormSMulClass ℝ (Space d →L[ℝ] ℝ)`), which is not found when `NormedSpace ℝ (Space d)` arises only as a nested subgoal through `InnerProductSpace.toNormedSpace`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The normed space structure on `Space d`, registered directly. It is definitionally the one underlying the inner product space structure, but registering it as its own instance is needed for typeclass search to find the operator-norm structure on `Space d →L[ℝ] ℝ` (for example `NormSMulClass ℝ (Space d →L[ℝ] ℝ)`), which is not found when `NormedSpace ℝ (Space d)` arises only as a nested subgoal through `InnerProductSpace.toNormedSpace`. -/
noncomputable instance Space.instNormedSpaceReal {d} : NormedSpace ℝ (Space d) := InnerProductSpace.toNormedSpace
