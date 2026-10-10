import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrame
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameIsInertial
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameIsMetricConserved
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameIsInertialIsMetricConserved
import AFTD.Kb.Physics.TimeVaddVal
import AFTD.Kb.Physics.TimeVsubEqVal
import AFTD.Kb.Physics.TimeInstNonempty
import AFTD.Kb.Physics.TimeInstVAddReal
import AFTD.Kb.Physics.TimeInstVSubReal
import AFTD.Kb.Physics.TimeInstAddTorsorReal
import AFTD.Kb.Physics.TimeInstMetricSpace
import AFTD.Kb.Physics.TimeInstNormedAddTorsorReal
import AFTD.Kb.Physics.TimeInstChartedSpaceReal
import AFTD.Kb.Physics.TimeInstIsManifoldRealModelWithCornersSelfTopWithTopENat

/-!
# ClassicalMechanics.ReferenceFrame.instFactIsMetricConservedOfIsInertial

Topic: classical_mechanics   Node: b9ca3408df34

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.ReferenceFrame.instFactIsMetricConservedOfIsInertial`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/ReferenceFrame.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Inertiality provides the conserved metric needed for metric operations on frame vectors.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.ReferenceFrame in
variable {d : ℕ} in
variable {frame : ReferenceFrame d} in
/-- Inertiality provides the conserved metric needed for metric operations on frame vectors. -/
noncomputable instance ClassicalMechanics.ReferenceFrame.instFactIsMetricConservedOfIsInertial [h : Fact frame.IsInertial] : Fact frame.IsMetricConserved := ⟨h.out.isMetricConserved⟩
