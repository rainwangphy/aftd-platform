import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroFunMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceELpNormMk

/-!
# QuantumMechanics.OneDimension.HilbertSpace.schwartzIncl

Topic: quantum_mechanics   Node: 73170047b3c3

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.schwartzIncl`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/SchwartzSubmodule.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The continuous linear map including Schwartz functions into the hilbert space.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
open SchwartzMap InnerProductSpace in
/-- The continuous linear map including Schwartz functions into the hilbert space. -/
noncomputable def QuantumMechanics.OneDimension.HilbertSpace.schwartzIncl : 𝓢(ℝ, ℂ) →L[ℂ] HilbertSpace :=
  SchwartzMap.toLpCLM ℂ (E := ℝ) ℂ 2 MeasureTheory.volume
