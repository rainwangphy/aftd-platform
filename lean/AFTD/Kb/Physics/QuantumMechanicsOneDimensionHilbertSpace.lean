import AFTD.Prelude

/-!
# QuantumMechanics.OneDimension.HilbertSpace

Topic: quantum_mechanics   Node: 1599647c5827

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Hilbert space for a one dimensional quantum system is defined as the space of almost-everywhere equal equivalence classes of square integrable functions from `ℝ` to `ℂ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The Hilbert space for a one dimensional quantum system is defined as the space of almost-everywhere equal equivalence classes of square integrable functions from `ℝ` to `ℂ`. -/
noncomputable abbrev QuantumMechanics.OneDimension.HilbertSpace := MeasureTheory.Lp (α := ℝ) ℂ 2
