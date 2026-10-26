import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianFactorShapes
import AFTD.Kb.Tcs.MondrianPrimeSquareAreaFreeShapeBound
import AFTD.Kb.Tcs.MondrianPrimeSquareAreaMiddleShapeBound

/-!
# mondrian_prime_square_area_shape_bound

Topic: combinatorics   Node: 116f694f4d20

Provenance: helper lemma. Helper for OP-280 and mondrian_no_perfect_prime_mul_prime_pow. Related work: arXiv:2610.19193, Section 1 (the zero-defect question); arXiv:2007.09639, Theorem 4.1 (prime-power and small prime-product exclusions).

For distinct primes p and q and t+r=2e with positive r, at most 2r unordered shapes of area q^2 times p^t fit in the q times p^e square.
-/

theorem mondrian_prime_square_area_shape_bound (p q e t r : ℕ) (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hpq : p ≠ q) (htr : t + r = 2 * e) (hr : 0 < r) :
    (mondrian_factor_shapes (q * p ^ e) (q ^ 2 * p ^ t)).card ≤ 2 * r := by
  have h1 := mondrian_prime_square_area_free_shape_bound p q e t r hp hq hpq htr
  have h2 := mondrian_prime_square_area_middle_shape_bound p q e t r hp hq hpq htr hr
  have hh := Finset.card_filter_add_card_filter_not
    (s := mondrian_factor_shapes (q * p ^ e) (q ^ 2 * p ^ t))
    (fun d : ℕ × ℕ => ¬ q ∣ d.1 ∨ ¬ q ∣ d.2)
  simp only [not_or, not_not] at hh
  omega
