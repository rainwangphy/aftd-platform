import AFTD.Prelude
import AFTD.Kb.Physics.IteratedDerivTanhDifferentiable

/-!
# iteratedDeriv_tanh_const_mul

Topic: classical_mechanics   Node: 3ea17269db9a

Provenance: formalization of a published result. Source: Physlib, `iteratedDeriv_tanh_const_mul`. Lean proof by Afiq Hatta, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Trigonometry/Tanh.lean (Copyright (c) 2025 Afiq Hatta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Iterated derivative for scaled tanh
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Real in
open NNReal in
open Field in
open scoped ContDiff in
/-- Iterated derivative for scaled tanh -/
lemma iteratedDeriv_tanh_const_mul (n : ℕ) (κ : ℝ) : ∀ x : ℝ,
    iteratedDeriv n (fun y => Real.tanh (κ * y)) x = κ^n * (iteratedDeriv n Real.tanh) (κ * x) := by
  induction n with
  | zero =>
    rw [iteratedDeriv_zero]
    field_simp
    simp
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have h' : iteratedDeriv n (fun y => tanh (κ * y)) =
        fun x => κ ^ n * iteratedDeriv n tanh (κ * x) := by
      funext x
      rw [ih]
    rw [h']
    simp only [deriv_const_mul_field']
    have h'': (fun x => iteratedDeriv n tanh (κ * x)) =
        (iteratedDeriv n tanh) ∘ (fun x => κ * x) := by
      funext x
      simp
    rw [h'']
    intro x
    rw [deriv_comp, ← iteratedDeriv_succ]
    have h''': deriv (fun x => κ * x) = fun x => κ := by
      funext x
      rw [deriv_const_mul, ← Function.id_def]
      field_simp
      simp only [deriv_id', mul_one]
      apply differentiable_id
    rw [h''']
    field_simp
    ring
    apply iteratedDeriv_tanh_differentiable
    fun_prop
