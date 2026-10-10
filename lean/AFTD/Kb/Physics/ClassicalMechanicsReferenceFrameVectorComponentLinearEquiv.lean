import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrame
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVector
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorComponentEquiv
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstAddCommGroup
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstModuleReal

/-!
# ClassicalMechanics.ReferenceFrame.Vector.componentLinearEquiv

Topic: classical_mechanics   Node: 112954218bc1

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.ReferenceFrame.Vector.componentLinearEquiv`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/ReferenceFrame.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Linear equivalence between frame vectors and coordinate components.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.ReferenceFrame ClassicalMechanics.ReferenceFrame.Vector in
variable {d : ℕ} in
variable {frame : ReferenceFrame d} in
/-- Linear equivalence between frame vectors and coordinate components. -/
noncomputable def ClassicalMechanics.ReferenceFrame.Vector.componentLinearEquiv : frame.Vector ≃ₗ[ℝ] (Fin d → ℝ) :=
  {componentEquiv with map_add' _ _ := rfl, map_smul' _ _ := rfl}
