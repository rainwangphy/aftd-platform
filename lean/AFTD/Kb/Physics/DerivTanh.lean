import AFTD.Prelude

/-!
# deriv_tanh

Topic: classical_mechanics   Node: 4178278d5329

Provenance: formalization of a published result. Source: Physlib, `deriv_tanh`. Lean proof by Afiq Hatta, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Trigonometry/Tanh.lean (Copyright (c) 2025 Afiq Hatta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The derivative of tanh(x) is 1 - tanh(x)^2
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Real in
open NNReal in
open Field in
open scoped ContDiff in
/-- The derivative of tanh(x) is 1 - tanh(x)^2 -/
lemma deriv_tanh : deriv Real.tanh = fun x => 1 - Real.tanh x ^ 2 := by
  have h: deriv (sinh / cosh) = fun x => 1 - Real.tanh x ^ 2 := by
    funext x
    rw [deriv_div, Real.deriv_sinh, Real.deriv_cosh]
    field_simp
    rw [sq, sq, tanh_eq_sinh_div_cosh]
    field_simp
    · apply Real.differentiable_sinh
    · apply Real.differentiable_cosh
    · exact ne_of_gt (Real.cosh_pos x)
  have h': Real.tanh = (sinh / cosh) := by
    funext x
    rw [Pi.div_apply, tanh_eq_sinh_div_cosh]
  nth_rewrite 1 [h']
  apply h
