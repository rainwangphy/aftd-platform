import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.SUSYN1InstModuleChiralModule

/-!
# QuantumMechanics.OneDimension.HilbertSpace.toBra

Topic: quantum_mechanics   Node: fa2fff21df9b

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.toBra`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The anti-linear map from the Hilbert space to it's dual.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module MeasureTheory in
open InnerProductSpace in
/-- The anti-linear map from the Hilbert space to it's dual. -/
noncomputable def QuantumMechanics.OneDimension.HilbertSpace.toBra : HilbertSpace →ₛₗ[starRingEnd ℂ] StrongDual ℂ HilbertSpace :=
  InnerProductSpace.toDual ℂ HilbertSpace
