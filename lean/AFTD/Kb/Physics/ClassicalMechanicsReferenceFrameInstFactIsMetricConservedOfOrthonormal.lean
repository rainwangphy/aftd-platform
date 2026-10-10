import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrame
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameOrthonormal
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameIsMetricConserved
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameOrthonormalIsMetricConserved
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
# ClassicalMechanics.ReferenceFrame.instFactIsMetricConservedOfOrthonormal

Topic: classical_mechanics   Node: be9c1392de08

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.ReferenceFrame.instFactIsMetricConservedOfOrthonormal`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/ReferenceFrame.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ClassicalMechanics.ReferenceFrame.instFactIsMetricConservedOfOrthonormal
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.ReferenceFrame in
variable {d : ℕ} in
variable {frame : ReferenceFrame d} in
noncomputable instance ClassicalMechanics.ReferenceFrame.instFactIsMetricConservedOfOrthonormal [h : Fact frame.Orthonormal] : Fact frame.IsMetricConserved := ⟨h.out.isMetricConserved⟩
