import AFTD.Prelude

/-!
# QuantumMechanics.OneDimension.HilbertSpace.positionState

Topic: quantum_mechanics   Node: 30816c295c71

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.positionState`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/PositionStates.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Position state as a member of the dual of the Schwartz submodule of the Hilbert space.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory SchwartzMap in
/-- Position state as a member of the dual of the Schwartz submodule of the Hilbert space. -/
noncomputable def QuantumMechanics.OneDimension.HilbertSpace.positionState (x : ℝ) : 𝓢(ℝ, ℂ) →L[ℂ] ℂ := TemperedDistribution.delta x
