import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrame
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameParticle
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameIsInertial
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVector
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstAddCommGroup
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstModuleReal
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstTopologicalSpace
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameParticleVelocity
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameParticleInstFactDifferentiableRealVectorPosOfIsInertial

/-!
# ClassicalMechanics.ReferenceFrame.Particle.instFactDifferentiableRealVectorVelocity

Topic: classical_mechanics   Node: 612e4beb3c54

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.ReferenceFrame.Particle.instFactDifferentiableRealVectorVelocity`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/PointParticle/Basic.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Velocity is differentiable in an inertial frame.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.ReferenceFrame ClassicalMechanics.ReferenceFrame.Particle in
open scoped BigOperators Classical in
variable {d : ℕ} {frame : ReferenceFrame d} in
variable (particle : frame.Particle) in
/-- Velocity is differentiable in an inertial frame. -/
noncomputable instance ClassicalMechanics.ReferenceFrame.Particle.instFactDifferentiableRealVectorVelocity [h : Fact frame.IsInertial] : Fact (Differentiable ℝ particle.velocity) :=
  ⟨particle.pos_twice_differentiable h.out |>.right⟩
