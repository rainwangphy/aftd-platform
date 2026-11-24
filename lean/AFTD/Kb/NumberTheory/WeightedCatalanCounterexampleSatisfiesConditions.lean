import AFTD.Prelude
import AFTD.Kb.NumberTheory.ForwardDiff
import AFTD.Kb.NumberTheory.IterForwardDiff
import AFTD.Kb.NumberTheory.BinaryDigitSum
import AFTD.Kb.NumberTheory.WeightedCatalanPoly
import AFTD.Kb.NumberTheory.WeightedCatalanPolyZero
import AFTD.Kb.NumberTheory.WeightedCatalanPolyOneSubZero

/-!
# weighted_catalan_counterexample_satisfies_conditions

Topic: elementary_number_theory   Node: 58f9530c3650

Provenance: formalization of a published result. Source: arXiv:2611.26953, Lemma 7

For every integer t, the polynomial b_t satisfies: b_t(0) is odd; 2^(k - s_2(k)) divides (Δ^k b_t)(x) for all k ≥ 2 and all natural numbers x, where s_2(k) is the sum of the binary digits of k; and b_t(0) ≡ b_t(1) mod 4.
-/

/-- One step of the forward-difference iteration. -/
private lemma weighted_catalan_counterexample_satisfies_conditions_iter_succ (k : ℕ) (f : ℕ → ℤ) :
    iter_forward_diff (k + 1) f = forward_diff (iter_forward_diff k f) := by
  simp only [iter_forward_diff]
  exact Function.iterate_succ_apply' forward_diff k f

/-- The forward difference of the zero function vanishes. -/
private lemma weighted_catalan_counterexample_satisfies_conditions_forward_diff_zero :
    forward_diff (fun _ => (0 : ℤ)) = fun _ => 0 := by
  funext x
  simp [forward_diff]

/-- The fourth forward difference of the cubic b_t vanishes. -/
private lemma weighted_catalan_counterexample_satisfies_conditions_fourth_diff (t : ℤ) (x : ℕ) :
    iter_forward_diff 4 (weighted_catalan_poly t) x = 0 := by
  simp only [iter_forward_diff, forward_diff, Function.iterate_succ, Function.iterate_zero,
    Function.comp_apply, id_eq, weighted_catalan_poly]
  push_cast
  ring

/-- Every forward difference of b_t of order at least four vanishes. -/
private lemma weighted_catalan_counterexample_satisfies_conditions_iter_eq_zero (t : ℤ) :
    ∀ k ≥ 4, iter_forward_diff k (weighted_catalan_poly t) = fun _ => 0 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => funext x; exact weighted_catalan_counterexample_satisfies_conditions_fourth_diff t x
  | succ n hn ih =>
      rw [weighted_catalan_counterexample_satisfies_conditions_iter_succ, ih]
      exact weighted_catalan_counterexample_satisfies_conditions_forward_diff_zero

/-- The polynomial b_t satisfies the three conditions of the 2-adic valuation conjecture. -/
theorem weighted_catalan_counterexample_satisfies_conditions (t : ℤ) :
    Odd (weighted_catalan_poly t 0) ∧
    (∀ k ≥ 2, ∀ x : ℕ, (2 : ℤ) ^ (k - binary_digit_sum k) ∣ iter_forward_diff k (weighted_catalan_poly t) x) ∧
    (weighted_catalan_poly t 0 ≡ weighted_catalan_poly t 1 [ZMOD 4]) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [weighted_catalan_poly_zero]; exact odd_one
  · intro k hk x
    rcases Nat.lt_or_ge k 4 with h | h
    · interval_cases k
      · have h2 : binary_digit_sum 2 = 1 := by decide
        rw [h2]
        norm_num
        refine ⟨3 * ((4 * t + 1) * (↑x + 1)) - 1, ?_⟩
        simp only [iter_forward_diff, forward_diff, Function.iterate_succ, Function.iterate_zero,
          Function.comp_apply, id_eq, weighted_catalan_poly]
        push_cast
        ring
      · have h3 : binary_digit_sum 3 = 2 := by decide
        rw [h3]
        norm_num
        refine ⟨3 * (4 * t + 1), ?_⟩
        simp only [iter_forward_diff, forward_diff, Function.iterate_succ, Function.iterate_zero,
          Function.comp_apply, id_eq, weighted_catalan_poly]
        push_cast
        ring
    · rw [weighted_catalan_counterexample_satisfies_conditions_iter_eq_zero t k h]
      exact dvd_zero _
  · rw [Int.modEq_iff_dvd, weighted_catalan_poly_one_sub_zero]
    exact dvd_mul_right 4 t
