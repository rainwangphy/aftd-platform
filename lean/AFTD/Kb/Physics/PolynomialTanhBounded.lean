import AFTD.Prelude
import AFTD.Kb.Physics.PolynomialBoundedOnInterval

/-!
# polynomial_tanh_bounded

Topic: classical_mechanics   Node: cc277cc3b98e

Provenance: formalization of a published result. Source: Physlib, `polynomial_tanh_bounded`. Lean proof by Afiq Hatta, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Trigonometry/Tanh.lean (Copyright (c) 2025 Afiq Hatta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a polynomial P, show that P (tanh x) is bounded on the real line
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Real in
open NNReal in
open Field in
open scoped ContDiff in
/-- For a polynomial P, show that P (tanh x) is bounded on the real line -/
lemma polynomial_tanh_bounded (P : Polynomial ℝ) :
    ∃ C : ℝ, ∀ x : ℝ, |P.eval (Real.tanh x)| ≤ C := by
  -- Since tanh maps to (-1, 1), it maps to [-1+ε, 1-ε] for any ε > 0
  -- But more directly, tanh maps to (-1, 1) ⊆ [-1, 1]
  have h_range : ∀ x : ℝ, Real.tanh x ∈ Set.Icc (-1) 1 := by
    intro x
    constructor
    · exact le_of_lt (neg_one_lt_tanh x)
    · exact le_of_lt (tanh_lt_one x)
  -- Apply polynomial boundedness on [-1, 1]
  obtain ⟨M, hM⟩ := polynomial_bounded_on_interval P (-1) 1
  use M
  intro x
  exact hM (Real.tanh x) (h_range x)
