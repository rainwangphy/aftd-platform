import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpace
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceMk
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceCoeMkAe
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceZeroFunMemHS

/-!
# QuantumMechanics.OneDimension.HilbertSpace.eLpNorm_mk

Topic: quantum_mechanics   Node: 9d73d25e2a6d

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.eLpNorm_mk`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.HilbertSpace.eLpNorm_mk
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module MeasureTheory in
open InnerProductSpace in
@[simp]
lemma QuantumMechanics.OneDimension.HilbertSpace.eLpNorm_mk {f : ℝ → ℂ} {hf : MemHS f} : eLpNorm (mk hf) 2 volume = eLpNorm f 2 volume :=
  MeasureTheory.eLpNorm_congr_ae (coe_mk_ae hf)
