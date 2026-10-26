import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianNoPerfectTwoPrimeArea
import AFTD.Kb.Tcs.MondrianNoPerfectPrimePowerArea
import AFTD.Kb.Tcs.MondrianPartitionAreaOneImpossible
import AFTD.Kb.Tcs.MondrianPartitionBounds
import AFTD.Kb.Tcs.MondrianDefectZeroEqual
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianRectWidth

/-!
# mondrian_perfect_area_three_prime_factors

Topic: combinatorics   Node: 230a7aab2581

Provenance: helper lemma. Corollary of mondrian_no_perfect_two_prime_area for OP-280, arXiv:2610.19193, Section 1.

Every tile area in a perfect admissible integer square partition has at least three distinct prime factors.
-/

theorem mondrian_perfect_area_three_prime_factors (n : ℕ)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hP : mondrian_is_partition n P)
    (hz : mondrian_defect P = 0) (r : ℕ × ℕ × ℕ × ℕ) (hr : r ∈ P) :
    3 ≤ (mondrian_rect_area r).primeFactors.card := by
  have hb := mondrian_partition_bounds n P hP r hr
  have hw := hb.2.2.1
  have hh := hb.2.2.2.1
  have hA : mondrian_rect_area r ≠ 0 := by
    dsimp [mondrian_rect_area]
    positivity
  by_contra! hc
  have h_cases : (mondrian_rect_area r).primeFactors.card = 0 ∨
      (mondrian_rect_area r).primeFactors.card = 1 ∨
      (mondrian_rect_area r).primeFactors.card = 2 := by omega
  rcases h_cases with h0 | h1 | h2
  · rw [Finset.card_eq_zero] at h0
    have h := Nat.prod_primeFactors_pow_factorization hA
    rw [h0] at h
    simp only [Finset.prod_empty] at h
    apply mondrian_partition_area_one_impossible n P hP
    intro s hs
    exact (mondrian_defect_zero_equal P hz s r hs hr).trans h
  · rw [Finset.card_eq_one] at h1
    obtain ⟨p, hp⟩ := h1
    have hp_mem : p ∈ (mondrian_rect_area r).primeFactors := by simp [hp]
    have hp_prime : Nat.Prime p := (Nat.mem_primeFactors.mp hp_mem).1
    have h := Nat.prod_primeFactors_pow_factorization hA
    rw [hp] at h
    simp only [Finset.prod_singleton] at h
    apply mondrian_no_perfect_prime_power_area p ((mondrian_rect_area r).factorization p) n hp_prime P hP hz
    intro s hs
    exact (mondrian_defect_zero_equal P hz s r hs hr).trans h
  · rw [Finset.card_eq_two] at h2
    rcases h2 with ⟨p, q, hpq, hpq_set⟩
    have hp_mem : p ∈ (mondrian_rect_area r).primeFactors := by simp [hpq_set]
    have hq_mem : q ∈ (mondrian_rect_area r).primeFactors := by simp [hpq_set]
    have hp_prime : Nat.Prime p := (Nat.mem_primeFactors.mp hp_mem).1
    have hq_prime : Nat.Prime q := (Nat.mem_primeFactors.mp hq_mem).1
    have h := Nat.prod_primeFactors_pow_factorization hA
    rw [hpq_set] at h
    rw [Finset.prod_pair hpq] at h
    apply mondrian_no_perfect_two_prime_area p q ((mondrian_rect_area r).factorization q) ((mondrian_rect_area r).factorization p) n hp_prime hq_prime hpq P hP hz
    intro s hs
    exact (mondrian_defect_zero_equal P hz s r hs hr).trans (h.trans (mul_comm _ _))
