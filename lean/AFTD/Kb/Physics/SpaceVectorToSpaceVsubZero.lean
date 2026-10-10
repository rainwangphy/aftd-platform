import AFTD.Prelude
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.SpaceInstVSubEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceVectorToSpace
import AFTD.Kb.Physics.SpaceInstZero
import AFTD.Kb.Physics.SpaceInstAddTorsorEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceValEqIff
import AFTD.Kb.Physics.SpaceVaddVal
import AFTD.Kb.Physics.SpaceVaddApply
import AFTD.Kb.Physics.SpaceVsubApply
import AFTD.Kb.Physics.SpaceZeroVal
import AFTD.Kb.Physics.SpaceZeroApply
import AFTD.Kb.Physics.SpaceVectorToSpaceApply
import AFTD.Kb.Physics.SpaceInstCoeFunForallFinReal
import AFTD.Kb.Physics.SpaceInstNonempty
import AFTD.Kb.Physics.SpaceInstSubsingletonOfNatNat
import AFTD.Kb.Physics.SpaceInstVAddEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstAddActionEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstDist
import AFTD.Kb.Physics.SpaceInstPseudoMetricSpace
import AFTD.Kb.Physics.SpaceInstNormedAddTorsorEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstMetricSpace
import AFTD.Kb.Physics.SpaceInstNontrivial
import AFTD.Kb.Physics.SpaceInstChartedSpaceEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceInstIsManifoldRealEuclideanSpaceFinModelWithCornersSelfTopWithTopENat

/-!
# Space.vectorToSpace_vsub_zero

Topic: classical_mechanics   Node: 24b9369e6bfd

Provenance: formalization of a published result. Source: Physlib, `Space.vectorToSpace_vsub_zero`. Lean proof by Shaopeng Zhu, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Origin.lean (Copyright (c) 2026 Shaopeng Zhu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.vectorToSpace_vsub_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
lemma Space.vectorToSpace_vsub_zero {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    vectorToSpace v -ᵥ (0 : Space d) = v := by
  ext i
  simp [vectorToSpace]
