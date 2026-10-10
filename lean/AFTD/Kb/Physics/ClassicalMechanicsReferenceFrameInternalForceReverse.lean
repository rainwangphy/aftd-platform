import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrame
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameInternalForce
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameForce
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVector
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstAddCommGroup

/-!
# ClassicalMechanics.ReferenceFrame.InternalForce.reverse

Topic: classical_mechanics   Node: 38ffaea636c7

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.ReferenceFrame.InternalForce.reverse`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Force.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The equal-and-opposite force with source and target exchanged.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.ReferenceFrame in
open scoped BigOperators Classical in
variable {d : ℕ} {frame : ReferenceFrame d} {Object : Type} in
/-- The equal-and-opposite force with source and target exchanged. -/
noncomputable def ClassicalMechanics.ReferenceFrame.InternalForce.reverse (force : frame.InternalForce Object) : frame.InternalForce Object where
  value := -force.value
  target := force.source
  source := force.target
  source_ne_target := force.source_ne_target.symm
