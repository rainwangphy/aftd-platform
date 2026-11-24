import AFTD.Prelude
import AFTD.Kb.NumberTheory.WeightedCatalanCounterexampleSatisfiesConditions
import AFTD.Kb.NumberTheory.WeightedCatalanFourPolyDvd
import AFTD.Kb.NumberTheory.CatalanFourPadicValuation
import AFTD.Kb.NumberTheory.WeightedCatalanPoly
import AFTD.Kb.NumberTheory.BinaryDigitSum
import AFTD.Kb.NumberTheory.IterForwardDiff
import AFTD.Kb.NumberTheory.WeightedCatalanFour

/-!
# weighted_catalan_conjecture_counterexample

Topic: elementary_number_theory   Node: f54b052e018a

Provenance: formalization of a published result. Source: arXiv:2611.26953, Theorem 6

For every integer t, the function weighted_catalan_poly t satisfies: weighted_catalan_poly t 0 is odd; for all natural numbers k ≥ 2 and all natural numbers x, 2^(k - binary_digit_sum k) divides iter_forward_diff k (weighted_catalan_poly t) x; weighted_catalan_poly t 0 ≡ weighted_catalan_poly t 1 [ZMOD 4]; and the 2-adic valuation padicValInt 2 of weighted_catalan_four (weighted_catalan_poly t) is not equal to padicValNat 2 (catalan 4).
-/

/-- Counterexamples to the 2-adic valuation conjecture for weighted Catalan numbers: b_t satisfies all three hypotheses but has unequal 2-adic valuation at n = 4. -/
theorem weighted_catalan_conjecture_counterexample (t : ℤ) :
    Odd (weighted_catalan_poly t 0) ∧
    (∀ k ≥ 2, ∀ x : ℕ, (2 : ℤ) ^ (k - binary_digit_sum k) ∣ iter_forward_diff k (weighted_catalan_poly t) x) ∧
    (weighted_catalan_poly t 0 ≡ weighted_catalan_poly t 1 [ZMOD 4]) ∧
    padicValInt 2 (weighted_catalan_four (weighted_catalan_poly t)) ≠ padicValNat 2 (catalan 4) := by
  refine ⟨(weighted_catalan_counterexample_satisfies_conditions t).1,
          (weighted_catalan_counterexample_satisfies_conditions t).2.1,
          (weighted_catalan_counterexample_satisfies_conditions t).2.2,
          ?_⟩
  rw [catalan_four_padic_valuation]
  intro hval
  have hdvd : 4 ∣ weighted_catalan_four (weighted_catalan_poly t) :=
    weighted_catalan_four_poly_dvd t
  have h2 : (2 : ℤ) ^ 2 ∣ weighted_catalan_four (weighted_catalan_poly t) := by
    simpa using hdvd
  have hiff := (padicValInt_dvd_iff_of_ne_one (p := 2) (by decide) 2 (weighted_catalan_four (weighted_catalan_poly t))).mp h2
  rcases hiff with heq | hle
  · have h0 : padicValInt 2 (0 : ℤ) = 0 := by
      unfold padicValInt
      simp
    rw [heq, h0] at hval
    contradiction
  · omega
