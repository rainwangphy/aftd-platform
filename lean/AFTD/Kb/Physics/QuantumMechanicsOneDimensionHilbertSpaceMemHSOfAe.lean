import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroFunMemHS

/-!
# QuantumMechanics.OneDimension.HilbertSpace.memHS_of_ae

Topic: quantum_mechanics   Node: fcd15d7fc41c

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.memHS_of_ae`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.HilbertSpace.memHS_of_ae
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module MeasureTheory in
open InnerProductSpace in
lemma QuantumMechanics.OneDimension.HilbertSpace.memHS_of_ae {g : ℝ → ℂ} (f : ℝ → ℂ) (hf : MemHS f) (hfg : f =ᵐ[MeasureTheory.volume] g) :
    MemHS g := MemLp.ae_eq hfg hf
