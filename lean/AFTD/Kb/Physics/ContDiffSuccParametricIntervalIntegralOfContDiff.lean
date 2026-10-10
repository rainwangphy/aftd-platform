import AFTD.Prelude
import AFTD.Kb.Physics.ContDiffOneParametricIntervalIntegralOfContDiff
import AFTD.Kb.Physics.FderivApplyParametericIntervalIntegral

/-!
# contDiff_succ_parametric_intervalIntegral_of_contDiff

Topic: classical_mechanics   Node: 382de00e27e8

Provenance: formalization of a published result. Source: Physlib, `contDiff_succ_parametric_intervalIntegral_of_contDiff`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/ParametricIntegration.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

contDiff_succ_parametric_intervalIntegral_of_contDiff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open scoped InnerProductSpace in
variable {M N : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [ProperSpace M]
    [NormedAddCommGroup N] [NormedSpace ℝ N] in
open MeasureTheory in
lemma contDiff_succ_parametric_intervalIntegral_of_contDiff {n : ℕ} [FiniteDimensional ℝ M]
    {F : M → ℝ → N} (hf : ContDiff ℝ (n + 1) ↿F) :
    ContDiff ℝ (n + 1) (fun (x : M) => ∫ (t : ℝ) in 0..1, F x t ∂(volume)) := by
  induction' n with n ih generalizing F
  · exact contDiff_one_parametric_intervalIntegral_of_contDiff hf
  · rw [contDiff_succ_iff_fderiv]
    refine ⟨ContDiff.differentiable
      (contDiff_one_parametric_intervalIntegral_of_contDiff (hf.of_le (by simp))) (by simp), ?_⟩
    simp only [Nat.cast_add, Nat.cast_one, WithTop.add_eq_top, WithTop.natCast_ne_top,
      WithTop.one_ne_top, or_self, IsEmpty.forall_iff, true_and, contDiff_clm_apply_iff,
      fderiv_apply_parameteric_intervalIntegral (hf.of_le (by simp))]
    exact fun y => ih (by fun_prop)
