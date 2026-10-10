import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrame
import AFTD.Kb.Physics.Time
import AFTD.Kb.Physics.TimeInstAddTorsorReal
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
# ClassicalMechanics.ReferenceFrame.timeEquiv

Topic: classical_mechanics   Node: 2a17a43f15d6

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.ReferenceFrame.timeEquiv`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/ReferenceFrame.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Convert a frame's real-valued time coordinate into an instant in affine time.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics in
variable {d : ℕ} in
variable {frame : ReferenceFrame d} in
/-- Convert a frame's real-valued time coordinate into an instant in affine time. -/
noncomputable def ClassicalMechanics.ReferenceFrame.timeEquiv (frame : ReferenceFrame d) : ℝ ≃ᵃ[ℝ] Time :=
  AffineEquiv.vaddConst ℝ frame.timeOrigin
