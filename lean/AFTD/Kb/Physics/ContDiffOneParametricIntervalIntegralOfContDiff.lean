import AFTD.Prelude
import AFTD.Kb.Physics.HasFDerivAtParametricIntervalIntegralOfContDiff

/-!
# contDiff_one_parametric_intervalIntegral_of_contDiff

Topic: classical_mechanics   Node: aed240e9faef

Provenance: formalization of a published result. Source: Physlib, `contDiff_one_parametric_intervalIntegral_of_contDiff`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/ParametricIntegration.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

contDiff_one_parametric_intervalIntegral_of_contDiff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open scoped InnerProductSpace in
variable {M N : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [ProperSpace M]
    [NormedAddCommGroup N] [NormedSpace ℝ N] in
open MeasureTheory in
lemma contDiff_one_parametric_intervalIntegral_of_contDiff
    {F : M → ℝ → N} (hf : ContDiff ℝ 1 ↿F) :
    ContDiff ℝ 1 (fun (x : M) => ∫ (t : ℝ) in 0..1, F x t ∂(volume)) := by
  rw [contDiff_one_iff_hasFDerivAt]
  refine ⟨_, ?_, hasFDerivAt_parametric_intervalIntegral_of_contDiff hf⟩
  fun_prop
