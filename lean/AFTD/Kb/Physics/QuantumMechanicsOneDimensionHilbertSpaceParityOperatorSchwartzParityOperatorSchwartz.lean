import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceParityOperatorSchwartz

/-!
# QuantumMechanics.OneDimension.HilbertSpace.parityOperatorSchwartz_parityOperatorSchwartz

Topic: quantum_mechanics   Node: 807192d14143

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.parityOperatorSchwartz_parityOperatorSchwartz`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/OneDimension/Parity.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.HilbertSpace.parityOperatorSchwartz_parityOperatorSchwartz
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory SchwartzMap in
@[simp]
lemma QuantumMechanics.OneDimension.HilbertSpace.parityOperatorSchwartz_parityOperatorSchwartz (ψ : 𝓢(ℝ, ℂ)) :
    parityOperatorSchwartz (parityOperatorSchwartz ψ) = ψ := by
  ext x
  show ψ (- - x) = ψ x
  rw [neg_neg]
