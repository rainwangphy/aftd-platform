import AFTD.Prelude

/-!
# contDiff_tanh

Topic: classical_mechanics   Node: fae756b7b25d

Provenance: formalization of a published result. Source: Physlib, `contDiff_tanh`. Lean proof by Afiq Hatta, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Trigonometry/Tanh.lean (Copyright (c) 2025 Afiq Hatta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Tanh(x) is n times continuously differentiable for all n
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Real in
open NNReal in
open Field in
open scoped ContDiff in
/-- Tanh(x) is n times continuously differentiable for all n -/
lemma contDiff_tanh {n : ℕ} : ContDiff ℝ n tanh := by
  have hdiv : ContDiff ℝ n (fun x => Real.sinh x / Real.cosh x) := by
    apply ContDiff.div
    · exact contDiff_sinh
    · exact contDiff_cosh
    · intro x
      exact ne_of_gt (Real.cosh_pos x)
  conv =>
    enter [3, x]
    rw [tanh_eq_sinh_div_cosh]
  exact hdiv
