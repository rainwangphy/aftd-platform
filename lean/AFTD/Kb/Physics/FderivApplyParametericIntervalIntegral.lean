import AFTD.Prelude
import AFTD.Kb.Physics.HasFDerivAtParametricIntervalIntegralOfContDiff

/-!
# fderiv_apply_parameteric_intervalIntegral

Topic: classical_mechanics   Node: 9a5046226ca1

Provenance: formalization of a published result. Source: Physlib, `fderiv_apply_parameteric_intervalIntegral`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/ParametricIntegration.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

fderiv_apply_parameteric_intervalIntegral
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open scoped InnerProductSpace in
variable {M N : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [ProperSpace M]
    [NormedAddCommGroup N] [NormedSpace ℝ N] in
open MeasureTheory in
lemma fderiv_apply_parameteric_intervalIntegral
    {F : M → ℝ → N} (hf : ContDiff ℝ 1 ↿F) (x₀ : M) (v : M) :
    fderiv ℝ (fun (x : M) => ∫ (t : ℝ) in 0..1, F x t ∂(volume)) x₀ v =
      ∫ (t : ℝ) in 0..1, fderiv ℝ (F · t) x₀ v ∂(volume) := by
  rw [(hasFDerivAt_parametric_intervalIntegral_of_contDiff hf x₀).fderiv]
  refine ContinuousLinearMap.intervalIntegral_apply ?_ v
  apply Continuous.intervalIntegrable
  fun_prop
