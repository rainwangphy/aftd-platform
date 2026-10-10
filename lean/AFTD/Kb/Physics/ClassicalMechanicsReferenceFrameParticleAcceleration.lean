import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrame
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameParticle
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVector
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstAddCommGroup
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstModuleReal
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstTopologicalSpace
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameParticleVelocity

/-!
# ClassicalMechanics.ReferenceFrame.Particle.acceleration

Topic: classical_mechanics   Node: e966f344a345

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.ReferenceFrame.Particle.acceleration`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/PointParticle/Basic.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The particle's acceleration.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.ReferenceFrame ClassicalMechanics.ReferenceFrame.Particle in
open scoped BigOperators Classical in
variable {d : ℕ} {frame : ReferenceFrame d} in
variable (particle : frame.Particle) in
/-- The particle's acceleration. -/
noncomputable def ClassicalMechanics.ReferenceFrame.Particle.acceleration [Fact (Differentiable ℝ particle.pos)]
    [_h : Fact (Differentiable ℝ particle.velocity)] : ℝ → frame.Vector :=
  deriv particle.velocity
