import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply

/-!
# QuantumMechanics.OneDimension.HilbertSpace.MemHS

Topic: quantum_mechanics   Node: c980735500b9

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.MemHS`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The proposition `MemHS f` for a function `f : ℝ → ℂ` is defined to be true if the function `f` can be lifted to the Hilbert space.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module MeasureTheory in
open InnerProductSpace in
/-- The proposition `MemHS f` for a function `f : ℝ → ℂ` is defined to be true if the function `f` can be lifted to the Hilbert space. -/
noncomputable def QuantumMechanics.OneDimension.HilbertSpace.MemHS (f : ℝ → ℂ) : Prop := MemLp f 2 MeasureTheory.volume
