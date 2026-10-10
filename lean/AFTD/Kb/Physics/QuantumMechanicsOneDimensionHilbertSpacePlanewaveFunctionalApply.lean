import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpacePlanewaveFunctional

/-!
# QuantumMechanics.OneDimension.HilbertSpace.planewaveFunctional_apply

Topic: quantum_mechanics   Node: 6b00981563ab

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.planewaveFunctional_apply`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/PlaneWaves.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.HilbertSpace.planewaveFunctional_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory SchwartzMap TemperedDistribution in
open FourierTransform in
lemma QuantumMechanics.OneDimension.HilbertSpace.planewaveFunctional_apply (k : ℝ) (ψ : 𝓢(ℝ, ℂ)) :
    planewaveFunctional k ψ = 𝓕 ψ k := rfl
