import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpacePositionState

/-!
# QuantumMechanics.OneDimension.HilbertSpace.positionState_apply

Topic: quantum_mechanics   Node: bf6bbded4494

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.positionState_apply`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/PositionStates.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.HilbertSpace.positionState_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory SchwartzMap in
lemma QuantumMechanics.OneDimension.HilbertSpace.positionState_apply (x : ℝ) (ψ : 𝓢(ℝ, ℂ)) :
    positionState x ψ = ψ x := rfl
