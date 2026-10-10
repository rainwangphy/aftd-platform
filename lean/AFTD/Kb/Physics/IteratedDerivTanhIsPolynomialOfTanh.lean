import AFTD.Prelude
import AFTD.Kb.Physics.DerivTanh

/-!
# iteratedDeriv_tanh_is_polynomial_of_tanh

Topic: classical_mechanics   Node: 455dd54821c2

Provenance: formalization of a published result. Source: Physlib, `iteratedDeriv_tanh_is_polynomial_of_tanh`. Lean proof by Afiq Hatta, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Trigonometry/Tanh.lean (Copyright (c) 2025 Afiq Hatta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The nth derivative of Tanh(x) is a polynomial of Tanh(x)
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Real in
open NNReal in
open Field in
open scoped ContDiff in
/-- The nth derivative of Tanh(x) is a polynomial of Tanh(x) -/
lemma iteratedDeriv_tanh_is_polynomial_of_tanh (n : ℕ) : ∃ P : Polynomial ℝ, ∀ x,
    iteratedDeriv n Real.tanh x = P.eval (Real.tanh x) := by
  induction n with
  | zero =>
    rw [iteratedDeriv_zero]
    use Polynomial.X
    simp
  | succ n ih =>
    obtain ⟨P, h'⟩ := ih
    rw [iteratedDeriv_succ]
    have h'': iteratedDeriv n tanh = (fun x => Polynomial.eval (tanh x) P) := by
      funext x
      apply h'
    have h_comp : (fun x => Polynomial.eval (tanh x) P) = (fun t => P.eval t) ∘ tanh := by
      funext x
      simp [Function.comp_apply]
    rw [h'', h_comp]
    use Polynomial.derivative P * (1 - Polynomial.X^2)
    intro x
    rw [deriv_comp, Polynomial.deriv, deriv_tanh]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow,
      Polynomial.eval_X]
    case h.hh =>
      have h': Real.tanh = (sinh / cosh) := by
        funext x
        rw [Pi.div_apply, tanh_eq_sinh_div_cosh]
      rw [h']
      apply DifferentiableAt.div
      · apply Real.differentiable_sinh
      · apply Real.differentiable_cosh
      · exact ne_of_gt (Real.cosh_pos x)
    case h.hh₂ =>
      apply Polynomial.differentiableAt
