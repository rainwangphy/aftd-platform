import AFTD.Prelude
import AFTD.Kb.Physics.ContDiffTopTanh
import AFTD.Kb.Physics.IteratedDerivTanhBounded

/-!
# tanh_hasTemperateGrowth

Topic: classical_mechanics   Node: e210c7c518cc

Provenance: formalization of a published result. Source: Physlib, `tanh_hasTemperateGrowth`. Lean proof by Afiq Hatta, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Trigonometry/Tanh.lean (Copyright (c) 2025 Afiq Hatta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

tanh has temperate growth
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Real in
open NNReal in
open Field in
open scoped ContDiff in
/-- tanh has temperate growth -/
lemma tanh_hasTemperateGrowth : Function.HasTemperateGrowth Real.tanh := by
  constructor
  · apply contDiff_top_tanh
  · intro n
    use 0
    obtain ⟨C, hC⟩ := iteratedDeriv_tanh_bounded n
    use C
    intro x
    have h_equiv : ‖iteratedFDeriv ℝ n Real.tanh x‖ = |iteratedDeriv n Real.tanh x| := by
      rw [← iteratedFDerivWithin_univ]
      rw [← iteratedDerivWithin_univ]
      rw [← norm_eq_abs]
      rw [norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
    rw [h_equiv]
    simp only [pow_zero, mul_one]
    exact hC x
