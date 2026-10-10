import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrame
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameForce
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVector

/-!
# ClassicalMechanics.ReferenceFrame.InternalForce

Topic: classical_mechanics   Node: cb00e882f7ed

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.ReferenceFrame.InternalForce`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Force.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A force between two objects.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.ReferenceFrame in
open scoped BigOperators Classical in
variable {d : ℕ} {frame : ReferenceFrame d} {Object : Type} in
/-- A force between two objects. -/
structure ClassicalMechanics.ReferenceFrame.InternalForce (frame : ReferenceFrame d) (Object : Type) extends frame.Force Object where
  /-- The source object. -/
  source : Object
  source_ne_target : source ≠ target
