import AFTD.Prelude

/-!
# polynomial_bounded_on_interval

Topic: classical_mechanics   Node: 8422bac2d695

Provenance: formalization of a published result. Source: Physlib, `polynomial_bounded_on_interval`. Lean proof by Afiq Hatta, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Trigonometry/Tanh.lean (Copyright (c) 2025 Afiq Hatta. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a polynomial P, show it's bounded on any bounded interval
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Real in
open NNReal in
open Field in
open scoped ContDiff in
/-- For a polynomial P, show it's bounded on any bounded interval -/
lemma polynomial_bounded_on_interval (P : Polynomial ℝ) (a b : ℝ) :
    ∃ M : ℝ, ∀ x : ℝ, x ∈ Set.Icc a b → |P.eval x| ≤ M := by
  -- Polynomials are continuous
  have hcont : Continuous (fun x => P.eval x) := P.continuous
  -- Closed bounded intervals are compact
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  -- Continuous functions on compact sets are bounded
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn hcont.continuousOn
  use M
  exact hM
