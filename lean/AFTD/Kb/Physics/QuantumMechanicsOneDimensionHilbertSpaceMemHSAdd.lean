import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroFunMemHS

/-!
# QuantumMechanics.OneDimension.HilbertSpace.memHS_add

Topic: quantum_mechanics   Node: 641d6f2cd581

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.memHS_add`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.HilbertSpace.memHS_add
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module MeasureTheory in
open InnerProductSpace in
lemma QuantumMechanics.OneDimension.HilbertSpace.memHS_add {f g : ℝ → ℂ} (hf : MemHS f) (hg : MemHS g) :
    MemHS (f + g) := MeasureTheory.MemLp.add hf hg
