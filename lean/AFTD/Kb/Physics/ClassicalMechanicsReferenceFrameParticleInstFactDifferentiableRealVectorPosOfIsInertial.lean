import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrame
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameParticle
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameIsInertial
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVector
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstAddCommGroup
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstModuleReal
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstTopologicalSpace

/-!
# ClassicalMechanics.ReferenceFrame.Particle.instFactDifferentiableRealVectorPosOfIsInertial

Topic: classical_mechanics   Node: ff05e13bab56

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.ReferenceFrame.Particle.instFactDifferentiableRealVectorPosOfIsInertial`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/PointParticle/Basic.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Position is differentiable in an inertial frame.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.ReferenceFrame in
open scoped BigOperators Classical in
variable {d : ℕ} {frame : ReferenceFrame d} in
variable (particle : frame.Particle) in
/-- Position is differentiable in an inertial frame. -/
noncomputable instance ClassicalMechanics.ReferenceFrame.Particle.instFactDifferentiableRealVectorPosOfIsInertial [h : Fact frame.IsInertial] : Fact (Differentiable ℝ particle.pos) :=
  ⟨particle.pos_twice_differentiable h.out |>.left⟩
