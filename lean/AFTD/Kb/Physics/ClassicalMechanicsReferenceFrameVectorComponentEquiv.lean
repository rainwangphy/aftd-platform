import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrame
import AFTD.Kb.Physics.ClassicalMechanicsReferenceFrameVector

/-!
# ClassicalMechanics.ReferenceFrame.Vector.componentEquiv

Topic: classical_mechanics   Node: 67b5b4576409

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.ReferenceFrame.Vector.componentEquiv`. Lean proof by Raunak Chhatwal, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/ReferenceFrame.lean (Copyright (c) 2026 Raunak Chhatwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Equivalence between frame vectors and coordinate components
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ClassicalMechanics ClassicalMechanics.ReferenceFrame in
variable {d : ℕ} in
variable {frame : ReferenceFrame d} in
/-- Equivalence between frame vectors and coordinate components -/
noncomputable def ClassicalMechanics.ReferenceFrame.Vector.componentEquiv : frame.Vector ≃ (Fin d → ℝ) :=
  Equiv.mk components mk Eq.refl Eq.refl
