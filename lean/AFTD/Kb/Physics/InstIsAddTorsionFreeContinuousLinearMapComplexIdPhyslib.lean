import AFTD.Prelude

/-!
# instIsAddTorsionFreeContinuousLinearMapComplexId_physlib

Topic: quantum_mechanics   Node: 4f74680b351a

Provenance: formalization of a published result. Source: Physlib, `instIsAddTorsionFreeContinuousLinearMapComplexId_physlib`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/SpectralMeasure.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

instIsAddTorsionFreeContinuousLinearMapComplexId_physlib
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ContinuousLinearMap in
open MeasureTheory in
open Set in
noncomputable instance instIsAddTorsionFreeContinuousLinearMapComplexId_physlib (H : Type*) [SeminormedAddCommGroup H] [InnerProductSpace ℂ H] :
    IsAddTorsionFree (H →L[ℂ] H) where
  nsmul_right_injective n hn := by
    refine Function.HasLeftInverse.injective ⟨fun f ↦ (n : ℂ)⁻¹ • f, fun x ↦ ?_⟩
    simp [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, Nat.cast_ne_zero (R := ℂ), hn]
