import AFTD.Prelude
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.SpaceInstAddCommGroup
import AFTD.Kb.Physics.SpaceInstModuleReal
import AFTD.Kb.Physics.SpaceInstPseudoMetricSpace
import AFTD.Kb.Physics.SpaceInstNormedAddCommGroup
import AFTD.Kb.Physics.SpaceInstNormedSpaceReal
import AFTD.Kb.Physics.SpaceInstAddCommMonoid
import AFTD.Kb.Physics.SpaceEquivPi
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
import AFTD.Kb.Physics.SpaceSumApply
import AFTD.Kb.Physics.SpaceBasisReprApply
import AFTD.Kb.Physics.SpaceBasisReprSymmApply
import AFTD.Kb.Physics.SpaceBasisSelf
import AFTD.Kb.Physics.SpaceInnerBasis
import AFTD.Kb.Physics.SpaceBasisInner
import AFTD.Kb.Physics.SpaceFinrankEqDim
import AFTD.Kb.Physics.SpaceRankEqDim
import AFTD.Kb.Physics.SpaceFderivBasisRepr
import AFTD.Kb.Physics.SpaceFderivBasisReprSymm
import AFTD.Kb.Physics.SpaceInstCoeFunForallFinReal
import AFTD.Kb.Physics.SpaceInstNonempty
import AFTD.Kb.Physics.SpaceInstSubsingletonOfNatNat
import AFTD.Kb.Physics.SpaceInstVAddEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstAddActionEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstVSubEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstAddTorsorEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstDist
import AFTD.Kb.Physics.SpaceInstNormedAddTorsorEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstMetricSpace
import AFTD.Kb.Physics.SpaceInstNontrivial
import AFTD.Kb.Physics.SpaceInstChartedSpaceEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstIsManifoldRealEuclideanSpaceFinModelWithCornersSelfTopWithTopENat
import AFTD.Kb.Physics.SpaceInstZero
import AFTD.Kb.Physics.SpaceInstAdd
import AFTD.Kb.Physics.SpaceInstSMulReal
import AFTD.Kb.Physics.SpaceInstNorm
import AFTD.Kb.Physics.SpaceInstNeg
import AFTD.Kb.Physics.SpaceInstSeminormedAddCommGroup
import AFTD.Kb.Physics.SpaceInstInnerReal
import AFTD.Kb.Physics.SpaceInstInnerProductSpaceReal
import AFTD.Kb.Physics.SpaceInstMeasurableSpace
import AFTD.Kb.Physics.SpaceInstBorelSpace
import AFTD.Kb.Physics.SpaceInstFiniteDimensionalReal

/-!
# Space.mk_differentiable

Topic: classical_mechanics   Node: 1abad6b62bfe

Provenance: formalization of a published result. Source: Physlib, `Space.mk_differentiable`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Module.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.mk_differentiable
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
open ContDiff in
@[fun_prop]
lemma Space.mk_differentiable {d : ℕ} :
    Differentiable ℝ (fun (f : Fin d → ℝ) => (⟨f⟩ : Space d)) := (equivPi d).symm.differentiable
