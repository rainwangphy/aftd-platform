import AFTD.Prelude
import AFTD.Kb.Physics.Space
import AFTD.Kb.Physics.SpaceInstPseudoMetricSpace
import AFTD.Kb.Physics.SpaceInstChartedSpaceEuclideanSpaceRealFin
import AFTD.Kb.Physics.SpaceHomEuclideanSpaceSpace
import AFTD.Kb.Physics.SpaceValEqIff
import AFTD.Kb.Physics.SpaceVaddVal
import AFTD.Kb.Physics.SpaceVaddApply
import AFTD.Kb.Physics.SpaceVsubApply
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

/-!
# Space.instIsManifoldRealEuclideanSpaceFinModelWithCornersSelfTopWithTopENat

Topic: classical_mechanics   Node: a6831b1fee22

Provenance: formalization of a published result. Source: Physlib, `Space.instIsManifoldRealEuclideanSpaceFinModelWithCornersSelfTopWithTopENat`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.instIsManifoldRealEuclideanSpaceFinModelWithCornersSelfTopWithTopENat
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold Real in
instance Space.instIsManifoldRealEuclideanSpaceFinModelWithCornersSelfTopWithTopENat (d : ℕ) : IsManifold (𝓡 d) ⊤ (Space d) :=
  (homEuclideanSpaceSpace d).symm.toOpenPartialHomeomorph.isManifold_singleton (by simp)
