import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceMemHS
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceMemHSIff
import AFTD.Kb.Physics.QuantumMechanicsOneDimensionHilbertSpaceToBraApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirStarComp

/-!
# QuantumMechanics.OneDimension.HilbertSpace.zero_memHS

Topic: quantum_mechanics   Node: ca33e0e16d90

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HilbertSpace.zero_memHS`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/OneDimension/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.OneDimension.HilbertSpace.zero_memHS
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module MeasureTheory in
open InnerProductSpace in
@[simp]
lemma QuantumMechanics.OneDimension.HilbertSpace.zero_memHS : MemHS 0 := by
  change MemHS (fun x => (0 : ℂ))
  rw [memHS_iff]
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    integrable_fun_zero, and_true]
  fun_prop
