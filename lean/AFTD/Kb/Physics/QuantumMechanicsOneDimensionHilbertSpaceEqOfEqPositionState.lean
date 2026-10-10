import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpacePositionState

/-!
# QuantumMechanics.OneDimension.HilbertSpace.eq_of_eq_positionState

Topic: quantum_mechanics   Node: 460502a3167b

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.eq_of_eq_positionState`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/PositionStates.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Two elements of the `𝓢(ℝ, ℂ)` are equal if they are equal on all position states.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory SchwartzMap in
/-- Two elements of the `𝓢(ℝ, ℂ)` are equal if they are equal on all position states. -/
lemma QuantumMechanics.OneDimension.HilbertSpace.eq_of_eq_positionState {ψ1 ψ2 : 𝓢(ℝ, ℂ)}
    (h : ∀ x, positionState x ψ1 = positionState x ψ2) :
    ψ1 = ψ2 := by
  ext x
  exact h x
