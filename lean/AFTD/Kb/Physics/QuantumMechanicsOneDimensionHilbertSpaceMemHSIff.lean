import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply

/-!
# QuantumMechanics.OneDimension.HilbertSpace.memHS_iff

Topic: quantum_mechanics   Node: 71b0b1899a39

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.memHS_iff`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A function `f` satisfies `MemHS f` if and only if it is almost everywhere strongly measurable, and square integrable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module MeasureTheory in
open InnerProductSpace in
/-- A function `f` satisfies `MemHS f` if and only if it is almost everywhere strongly measurable, and square integrable. -/
lemma QuantumMechanics.OneDimension.HilbertSpace.memHS_iff {f : ℝ → ℂ} : MemHS f ↔
    AEStronglyMeasurable f ∧ Integrable (fun x => ‖f x‖ ^ 2) := by
  refine ⟨fun h => ⟨h.aestronglyMeasurable,
    (memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable).mp h⟩, ?_⟩
  rintro ⟨h1, h2⟩
  exact (memLp_two_iff_integrable_sq_norm h1).mpr h2
