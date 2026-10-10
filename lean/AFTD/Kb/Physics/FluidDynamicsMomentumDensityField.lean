import AFTD.Prelude
import AFTD.Kb.Physics.FluidDynamicsVectorField
import AFTD.Kb.Physics.SpaceValEqIff
import AFTD.Kb.Physics.SpaceVaddVal
import AFTD.Kb.Physics.SpaceVaddApply
import AFTD.Kb.Physics.SpaceVsubApply
import AFTD.Kb.Physics.TimeVaddVal
import AFTD.Kb.Physics.TimeVsubEqVal
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
import AFTD.Kb.Physics.TimeInstNonempty
import AFTD.Kb.Physics.TimeInstVAddReal
import AFTD.Kb.Physics.TimeInstVSubReal
import AFTD.Kb.Physics.TimeInstAddTorsorReal
import AFTD.Kb.Physics.TimeInstMetricSpace
import AFTD.Kb.Physics.TimeInstNormedAddTorsorReal
import AFTD.Kb.Physics.TimeInstChartedSpaceReal
import AFTD.Kb.Physics.TimeInstIsManifoldRealModelWithCornersSelfTopWithTopENat

/-!
# FluidDynamics.MomentumDensityField

Topic: fluid_dynamics   Node: 6c16174d0475

Provenance: formalization of a published result. Source: Physlib, `FluidDynamics.MomentumDensityField`. Lean proof by Florian Wiesner, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/FluidDynamics/Basic.lean (Copyright (c) 2026 Florian Wiesner. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A momentum density field on `d`-dimensional space.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A momentum density field on `d`-dimensional space. -/
abbrev FluidDynamics.MomentumDensityField (d : ℕ) := VectorField d
