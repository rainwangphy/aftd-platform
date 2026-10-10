import AFTD.Prelude
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.SpaceInstSMulReal
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

/-!
# Space.smul_val

Topic: classical_mechanics   Node: e6d4d8ea29f0

Provenance: formalization of a published result. Source: Physlib, `Space.smul_val`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Module.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.smul_val
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
lemma Space.smul_val {d : ℕ} (c : ℝ) (p : Space d) :
    (c • p).val = fun i => c * p.val i := rfl
