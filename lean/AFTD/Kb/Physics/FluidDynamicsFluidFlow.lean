import AFTD.Prelude
import AFTD.Kb.Physics.FluidDynamicsMassDensity
import AFTD.Kb.Physics.FluidDynamicsVelocityField
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
# FluidDynamics.FluidFlow

Topic: fluid_dynamics   Node: 5a417b75f8e9

Provenance: formalization of a published result. Source: Physlib, `FluidDynamics.FluidFlow`. Lean proof by Florian Wiesner, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/FluidDynamics/FluidFlow/Basic.lean (Copyright (c) 2026 Florian Wiesner. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The density and velocity fields of a fluid on `d`-dimensional space. These fields are the independent data needed for kinematics and mass transport. Quantities such as mass flux, momentum density, and material acceleration are derived from them. Dynamic and thermodynamic fields are introduced only by extension structures whose statements need them.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The density and velocity fields of a fluid on `d`-dimensional space. These fields are the independent data needed for kinematics and mass transport. Quantities such as mass flux, momentum density, and material acceleration are derived from them. Dynamic and thermodynamic fields are introduced only by extension structures whose statements need them. -/
structure FluidDynamics.FluidFlow (d : ℕ) where
  /-- The mass density field. -/
  rho : MassDensity d
  /-- The velocity field. -/
  velocity : VelocityField d
