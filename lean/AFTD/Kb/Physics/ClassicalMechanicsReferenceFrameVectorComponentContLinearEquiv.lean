import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrame
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVector
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstTopologicalSpace
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstAddCommGroup
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorInstModuleReal
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorComponentLinearEquiv
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVectorComponentEquiv

/-!
# ClassicalMechanics.ReferenceFrame.Vector.componentContLinearEquiv

Topic: classical_mechanics   Node: 2b55899eb0a2

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.ReferenceFrame.Vector.componentContLinearEquiv`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/ReferenceFrame.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Continuous linear equivalence between frame vectors and coordinate components.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.ReferenceFrame ClassicalMechanics.ReferenceFrame.Vector in
variable {d : ℕ} in
variable {frame : ReferenceFrame d} in
/-- Continuous linear equivalence between frame vectors and coordinate components. -/
noncomputable def ClassicalMechanics.ReferenceFrame.Vector.componentContLinearEquiv (frame : ReferenceFrame d) : frame.Vector ≃L[ℝ] (Fin d → ℝ) :=
  { componentLinearEquiv with
    continuous_toFun := continuous_induced_dom
    continuous_invFun := componentEquiv.homeomorph.continuous_invFun }
