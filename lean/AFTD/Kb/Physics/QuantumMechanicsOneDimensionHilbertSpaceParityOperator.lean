import AFTD.Prelude

/-!
# QuantumMechanics.OneDimension.HilbertSpace.parityOperator

Topic: quantum_mechanics   Node: 6fc64702d21e

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.parityOperator`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/OneDimension/Parity.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The parity operator is defined as linear map from `ℝ → ℂ` to itself, such that `ψ` is taken to `fun x => ψ (-x)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory SchwartzMap in
/-- The parity operator is defined as linear map from `ℝ → ℂ` to itself, such that `ψ` is taken to `fun x => ψ (-x)`. -/
noncomputable def QuantumMechanics.OneDimension.HilbertSpace.parityOperator : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun ψ := fun x => ψ (-x)
  map_add' ψ1 ψ2 := by
    funext x
    simp
  map_smul' a ψ1 := by
    funext x
    simp
