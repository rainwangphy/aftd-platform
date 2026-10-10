import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrame
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVector
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstAddCommGroup
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstModuleReal
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorComponentLinearEquiv
import AFTD.Kb.Physics.Time
import AFTD.Kb.Physics.TimeInstAddTorsorReal
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameTimeEquiv
import AFTD.Kb.Physics.TimeVaddVal
import AFTD.Kb.Physics.TimeVsubEqVal
import AFTD.Kb.Physics.TimeInstNonempty
import AFTD.Kb.Physics.TimeInstVAddReal
import AFTD.Kb.Physics.TimeInstVSubReal
import AFTD.Kb.Physics.TimeInstMetricSpace
import AFTD.Kb.Physics.TimeInstNormedAddTorsorReal
import AFTD.Kb.Physics.TimeInstChartedSpaceReal
import AFTD.Kb.Physics.TimeInstIsManifoldRealModelWithCornersSelfTopWithTopENat

/-!
# ClassicalMechanics.ReferenceFrame.Vector.dispEquiv

Topic: classical_mechanics   Node: ba924b277018

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.ReferenceFrame.Vector.dispEquiv`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/ReferenceFrame.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Equivalence between frame vectors and geometric displacements in space, defined by the frame's basis at time coordinate `t`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.ReferenceFrame ClassicalMechanics.ReferenceFrame.Vector in
variable {d : ℕ} in
variable {frame : ReferenceFrame d} in
/-- Equivalence between frame vectors and geometric displacements in space, defined by the frame's basis at time coordinate `t`. -/
noncomputable def ClassicalMechanics.ReferenceFrame.Vector.dispEquiv (t : ℝ) : frame.Vector ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  componentLinearEquiv.trans (frame.basis (frame.timeEquiv t)).equivFun.symm
