import AFTD.Prelude

/-!
# tanh_const_mul_iteratedDeriv_norm_eq_iteratedFDeriv_norm

Topic: classical_mechanics   Node: 329500b3781b

Provenance: formalization of a published result. Source: Physlib, `tanh_const_mul_iteratedDeriv_norm_eq_iteratedFDeriv_norm`. Lean proof by Afiq Hatta, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Trigonometry/Tanh.lean (Copyright (c) 2025 Afiq Hatta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Norm of Iterated derivative for scaled tanh is equal to the norm of its Fderiv
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Real in
open NNReal in
open Field in
open scoped ContDiff in
/-- Norm of Iterated derivative for scaled tanh is equal to the norm of its Fderiv -/
lemma tanh_const_mul_iteratedDeriv_norm_eq_iteratedFDeriv_norm (n : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ n (fun x => tanh (κ * x)) x‖
    = |iteratedDeriv n (fun x => tanh (κ * x)) x| := by
  rw [← iteratedFDerivWithin_univ, ← iteratedDerivWithin_univ, ← norm_eq_abs,
      norm_iteratedFDerivWithin_eq_norm_iteratedDerivWithin]
