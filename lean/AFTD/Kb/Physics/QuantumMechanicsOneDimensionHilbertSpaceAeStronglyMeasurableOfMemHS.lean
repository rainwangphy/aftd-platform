import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply

/-!
# QuantumMechanics.OneDimension.HilbertSpace.aeStronglyMeasurable_of_memHS

Topic: quantum_mechanics   Node: 79f3b64ad1b8

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.aeStronglyMeasurable_of_memHS`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.HilbertSpace.aeStronglyMeasurable_of_memHS
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module MeasureTheory in
open InnerProductSpace in
lemma QuantumMechanics.OneDimension.HilbertSpace.aeStronglyMeasurable_of_memHS {f : ℝ → ℂ} (h : MemHS f) : AEStronglyMeasurable f :=
  h.aestronglyMeasurable
