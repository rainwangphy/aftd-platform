import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrame

/-!
# ClassicalMechanics.ReferenceFrame.Vector

Topic: classical_mechanics   Node: 6b17dc0390f1

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.ReferenceFrame.Vector`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/ReferenceFrame.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `d` real components used to express a vector quantity relative to `frame`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics in
variable {d : ℕ} in
variable {frame : ReferenceFrame d} in
/-- The `d` real components used to express a vector quantity relative to `frame`. -/
structure ClassicalMechanics.ReferenceFrame.Vector (frame : ReferenceFrame d) where
  /-- One scalar coefficient for each axis of the frame. -/
  components : Fin d → ℝ
