import AFTD.Prelude
import AFTD.Kb.Physics.ContDiffTopTanh
import AFTD.Kb.Physics.IteratedDerivTanhBounded
import AFTD.Kb.Physics.TanhConstMulIteratedDerivNormEqIteratedFDerivNorm
import AFTD.Kb.Physics.IteratedDerivTanhConstMul

/-!
# tanh_const_mul_hasTemperateGrowth

Topic: classical_mechanics   Node: 91d5cbe88a39

Provenance: formalization of a published result. Source: Physlib, `tanh_const_mul_hasTemperateGrowth`. Lean proof by Afiq Hatta, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Trigonometry/Tanh.lean (Copyright (c) 2025 Afiq Hatta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

tanh(κx) has temperate growth
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Real in
open NNReal in
open Field in
open scoped ContDiff in
/-- tanh(κx) has temperate growth -/
@[fun_prop]
lemma tanh_const_mul_hasTemperateGrowth (κ : ℝ) :
    Function.HasTemperateGrowth (fun x => Real.tanh (κ * x)) := by
  constructor
  · have h : (fun x => Real.tanh (κ * x)) = (Real.tanh ∘ (fun x => κ * x)) :=
      rfl
    have h' : ContDiff ℝ ∞ (fun x => κ * x) := by
      have h'': (fun x : ℝ => κ * x) = fun x => κ • x := rfl
      rw [contDiff_infty, h'']
      intro n
      apply contDiff_const_smul
    rw [h]
    apply ContDiff.comp contDiff_top_tanh h'
  · intro n
    obtain ⟨D, hD⟩ := iteratedDeriv_tanh_bounded n
    use 0
    use D * (|κ| ^ n)
    intro x
    rw [tanh_const_mul_iteratedDeriv_norm_eq_iteratedFDeriv_norm, iteratedDeriv_tanh_const_mul]
    field_simp
    rw [abs_mul, abs_pow, mul_comm, mul_comm, mul_comm D (|κ| ^ n)]
    apply mul_le_mul_of_nonneg_left
    apply hD
    simp only [abs_nonneg, pow_nonneg]
