import AFTD.Prelude
import AFTD.Kb.Physics.IteratedDerivTanhIsPolynomialOfTanh
import AFTD.Kb.Physics.PolynomialTanhBounded

/-!
# iteratedDeriv_tanh_bounded

Topic: classical_mechanics   Node: cd028bbb7052

Provenance: formalization of a published result. Source: Physlib, `iteratedDeriv_tanh_bounded`. Lean proof by Afiq Hatta, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Trigonometry/Tanh.lean (Copyright (c) 2025 Afiq Hatta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The nth derivative of tanh is bounded on the real line
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Real in
open NNReal in
open Field in
open scoped ContDiff in
/-- The nth derivative of tanh is bounded on the real line -/
lemma iteratedDeriv_tanh_bounded (n : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, |iteratedDeriv n Real.tanh x| ≤ C := by
  obtain ⟨P, hP⟩ := iteratedDeriv_tanh_is_polynomial_of_tanh n
  obtain ⟨C, hC⟩ := polynomial_tanh_bounded P
  use C
  intro x
  rw [hP]
  exact hC x
