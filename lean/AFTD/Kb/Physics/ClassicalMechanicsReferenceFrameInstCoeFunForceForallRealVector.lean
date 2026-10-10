import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrame
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameForce
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVector

/-!
# ClassicalMechanics.ReferenceFrame.instCoeFunForceForallRealVector

Topic: classical_mechanics   Node: c7d5d7b3f47a

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.ReferenceFrame.instCoeFunForceForallRealVector`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/Force.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ClassicalMechanics.ReferenceFrame.instCoeFunForceForallRealVector
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.ReferenceFrame in
open scoped BigOperators Classical in
variable {d : ℕ} {frame : ReferenceFrame d} {Object : Type} in
noncomputable instance ClassicalMechanics.ReferenceFrame.instCoeFunForceForallRealVector : CoeFun (frame.Force Object) (fun _ => ℝ → frame.Vector) where
  coe := Force.value
