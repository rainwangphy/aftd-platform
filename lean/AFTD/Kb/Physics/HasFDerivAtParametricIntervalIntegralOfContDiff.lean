import AFTD.Prelude

/-!
# hasFDerivAt_parametric_intervalIntegral_of_contDiff

Topic: classical_mechanics   Node: bee5776fcc8a

Provenance: formalization of a published result. Source: Physlib, `hasFDerivAt_parametric_intervalIntegral_of_contDiff`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/ParametricIntegration.lean (Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

hasFDerivAt_parametric_intervalIntegral_of_contDiff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open scoped InnerProductSpace in
variable {M N : Type}
    [NormedAddCommGroup M] [NormedSpace ℝ M] [ProperSpace M]
    [NormedAddCommGroup N] [NormedSpace ℝ N] in
open MeasureTheory in
lemma hasFDerivAt_parametric_intervalIntegral_of_contDiff
    {F : M → ℝ → N} (hf : ContDiff ℝ 1 ↿F) (x₀ : M) :
    HasFDerivAt (fun (x : M) => ∫ (t : ℝ) in 0..1, F x t ∂(volume))
      (∫ (t : ℝ) in 0..1, fderiv ℝ (F · t) x₀ ∂(volume)) x₀ := by
  let F' : M → ℝ → M →L[ℝ] N := fun x t => fderiv ℝ (F · t) x
  let s (x₀) : Set M := Metric.closedBall x₀ 1
  have hF' : Continuous ↿F' := by fun_prop
  obtain ⟨a, ha⟩ := IsCompact.exists_isMaxOn (s := s x₀ ×ˢ Set.Icc (0 : ℝ) (1 : ℝ))
      ((isCompact_closedBall x₀ 1).prod isCompact_Icc)
      (f := fun (a : M × ℝ) => ‖F' a.1 a.2‖)
      (by simp [s])
      (continuous_norm.comp hF').continuousOn
  have hx := hf.differentiable (by simp)
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (s := s x₀)
    (F' := F') (bound := fun t => ‖F' a.1 a.2‖)
  · exact Metric.closedBall_mem_nhds x₀ one_pos
  · filter_upwards with x
    apply Continuous.aestronglyMeasurable
    fun_prop
  · apply Continuous.intervalIntegrable
    fun_prop
  · apply Continuous.aestronglyMeasurable
    exact Continuous.uncurry_left x₀ (by fun_prop)
  · filter_upwards with t h x hx
    exact ha.2 (Set.mk_mem_prod hx (Set.Ioc_subset_Icc_self (by simpa using h)))
  · exact intervalIntegrable_const
  · filter_upwards with t h x hx
    exact DifferentiableAt.hasFDerivAt (by fun_prop)
