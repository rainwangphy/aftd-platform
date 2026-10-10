import AFTD.Prelude
import AFTD.Kb.Physics.ContDiffSuccParametricIntervalIntegralOfContDiff

/-!
# contDiff_parametric_intervalIntegral_of_contDiff

Topic: classical_mechanics   Node: 9fc8518d4182

Provenance: formalization of a published result. Source: Physlib, `contDiff_parametric_intervalIntegral_of_contDiff`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/ParametricIntegration.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

contDiff_parametric_intervalIntegral_of_contDiff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open scoped InnerProductSpace in
variable {M N : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [ProperSpace M]
    [NormedAddCommGroup N] [NormedSpace ℝ N] in
open MeasureTheory in
lemma contDiff_parametric_intervalIntegral_of_contDiff {n : ℕ} {M : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [ProperSpace M] [FiniteDimensional ℝ M]
    {F : M → ℝ → N} (hf : ContDiff ℝ n ↿F) :
    ContDiff ℝ n (fun (x : M) => ∫ (t : ℝ) in 0..1, F x t ∂(volume)) := by
  induction' n with n ih generalizing F
  · exact contDiff_zero.mpr (by fun_prop)
  · exact contDiff_succ_parametric_intervalIntegral_of_contDiff (hf.of_le (by simp))
