import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrame
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVector
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstAddCommGroup
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstModuleReal

/-!
# ClassicalMechanics.ReferenceFrame.Vector.instSMulSubtypeRealLtOfNat

Topic: classical_mechanics   Node: f667f1268bf1

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.ReferenceFrame.Vector.instSMulSubtypeRealLtOfNat`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/ReferenceFrame.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Scalar multiplication by a positive real.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.ReferenceFrame ClassicalMechanics.ReferenceFrame.Vector in
variable {d : ℕ} in
variable {frame : ReferenceFrame d} in
/-- Scalar multiplication by a positive real. -/
noncomputable instance ClassicalMechanics.ReferenceFrame.Vector.instSMulSubtypeRealLtOfNat : SMul {x : ℝ // 0 < x} frame.Vector where
  smul c x := c.val • x
