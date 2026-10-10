import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrame
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameOrthonormal
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameIsMetricConserved
import AFTD.Kb.Physics.Time
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
# ClassicalMechanics.ReferenceFrame.Orthonormal.isMetricConserved

Topic: classical_mechanics   Node: 07113995f411

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.ReferenceFrame.Orthonormal.isMetricConserved`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/ReferenceFrame.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An orthonormal frame conserves its coordinate metric.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.ReferenceFrame in
variable {d : ℕ} in
variable {frame : ReferenceFrame d} in
/-- An orthonormal frame conserves its coordinate metric. -/
lemma ClassicalMechanics.ReferenceFrame.Orthonormal.isMetricConserved (h : frame.Orthonormal) : frame.IsMetricConserved := by
  intro t₁ t₂ i j
  rw [orthonormal_iff_ite.mp (h t₁) i j, orthonormal_iff_ite.mp (h t₂) i j]
