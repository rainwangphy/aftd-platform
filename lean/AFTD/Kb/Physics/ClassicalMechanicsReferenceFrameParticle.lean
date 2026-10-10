import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrame
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVector
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameIsInertial
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstAddCommGroup
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstModuleReal
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstTopologicalSpace

/-!
# ClassicalMechanics.ReferenceFrame.Particle

Topic: classical_mechanics   Node: 6d2ba054b9cf

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.ReferenceFrame.Particle`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/PointParticle/Basic.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A point particle in `frame`.
-/

set_option quotPrecheck false
open ClassicalMechanics ClassicalMechanics.ReferenceFrame
local notation "ℝ+" => {x : ℝ // 0 < x}

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.ReferenceFrame in
open scoped BigOperators Classical in
variable {d : ℕ} {frame : ReferenceFrame d} in
/-- A point particle in `frame`. -/
structure ClassicalMechanics.ReferenceFrame.Particle (frame : ReferenceFrame d) where
  /-- The particle's mass. -/
  mass : ℝ+
  /-- The particle's position in frame coordinates. -/
  pos : ℝ → frame.Vector
  pos_twice_differentiable :
    frame.IsInertial → Differentiable ℝ pos ∧ Differentiable ℝ (deriv pos)
