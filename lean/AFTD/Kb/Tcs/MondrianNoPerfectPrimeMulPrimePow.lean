import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianDefectZeroEqual
import AFTD.Kb.Tcs.MondrianFactorShapes
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianNoPerfectPrimePower
import AFTD.Kb.Tcs.MondrianPartitionBounds
import AFTD.Kb.Tcs.MondrianPartitionPrimeFreeShapeCountBound
import AFTD.Kb.Tcs.MondrianPerfectAreaProduct
import AFTD.Kb.Tcs.MondrianPerfectPartitionDiv
import AFTD.Kb.Tcs.MondrianPerfectPrimeFreeSideCounts
import AFTD.Kb.Tcs.MondrianPrimeAreaShapeBound
import AFTD.Kb.Tcs.MondrianPrimeFreeAreaShapeBound
import AFTD.Kb.Tcs.MondrianPrimeLogGap
import AFTD.Kb.Tcs.MondrianPrimeSquareAreaFreeShapeBound
import AFTD.Kb.Tcs.MondrianPrimeSquareAreaShapeBound
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianShapeBound
import AFTD.Kb.Tcs.MondrianTwiceExponentLtPrimePower
import AFTD.Kb.Tcs.MondrianTwoPrimeFactorPairEncoding
import AFTD.Kb.Tcs.MondrianRectDiv
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.Tcs.MondrianRectCells

/-!
# mondrian_no_perfect_prime_mul_prime_pow

Topic: combinatorics   Node: d7ee90a3b932

Provenance: original. Related work: Helper for OP-280 and mondrian_no_perfect_prime_mul_prime_pow. Related work: arXiv:2610.19193, Section 1 (the zero-defect question); arXiv:2007.09639, Theorem 4.1 (prime-power and small prime-product exclusions).

For every pair of distinct primes p and q and every natural exponent e, the square of side q times p^e has no perfect admissible integer rectangle partition.
-/

theorem mondrian_no_perfect_prime_mul_prime_pow (p q e : ℕ) (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hpq : p ≠ q) :
    ¬ ∃ P, mondrian_is_partition (q * p ^ e) P ∧ mondrian_defect P = 0 := by
  rintro ⟨P, hP, hz⟩
  obtain ⟨z, hzP⟩ : ∃ z, z ∈ P := by
    cases P with
    | nil => have := hP.1; simp at this
    | cons z P => exact ⟨z, by simp⟩
  let k := P.length
  let A := mondrian_rect_area z
  let r := k.factorization p
  let t := A.factorization p
  have hk : 2 ≤ k := hP.1
  have hzb := mondrian_partition_bounds (q * p ^ e) P hP z hzP
  have hA : 0 < A := Nat.mul_pos hzb.2.2.1 hzb.2.2.2.1
  have hareas : ∀ w ∈ P, mondrian_rect_area w = A :=
    fun w hw => mondrian_defect_zero_equal P hz w z hw hzP
  have heq : k * A = q ^ 2 * p ^ (2 * e) := by
    have hh := mondrian_perfect_area_product (q * p ^ e) P hP hz z hzP
    change k * A = (q * p ^ e) ^ 2 at hh
    rw [hh, mul_pow, ← pow_mul, Nat.mul_comm e 2]
  have hcard : k ≤ (mondrian_factor_shapes (q * p ^ e) A).card :=
    mondrian_shape_bound (q * p ^ e) A P hP hareas
  obtain ⟨b, s, hbs, hkrep, hArep, hrt⟩ := mondrian_two_prime_factor_pair_encoding p q (2 * e) 2 k A
    hp hq hpq (by omega) hA heq
  change k = q ^ b * p ^ r at hkrep
  change A = q ^ s * p ^ t at hArep
  change r + t = 2 * e at hrt
  have hs : s ≤ 2 := by omega
  by_cases hs2 : s = 2
  · have hb : b = 0 := by omega
    have hkp : k = p ^ r := by simpa only [hb, pow_zero, one_mul] using hkrep
    have hrpos : 0 < r := by
      by_contra hh
      have hr0 : r = 0 := by omega
      simp [hkp, hr0] at hk
    have hcap := mondrian_prime_square_area_shape_bound p q e t r hp hq hpq (by omega) hrpos
    have hArep' : A = q ^ 2 * p ^ t := by simpa only [hs2] using hArep
    rw [hArep'] at hcard
    have hpowcap : p ^ r ≤ 2 * r := by omega
    have hrle : r ≤ 2 := by
      by_contra hh
      have hgap := mondrian_twice_exponent_lt_prime_power p r hp.two_le (by omega)
      omega
    have hp2 : p = 2 := by
      interval_cases r
      · norm_num at hpowcap; have := hp.two_le; omega
      · norm_num at hpowcap; have := hp.two_le; nlinarith
    have hq3 : 3 ≤ q := by have := hq.two_le; omega
    have houter := mondrian_prime_square_area_free_shape_bound p q e t r hp hq hpq (by omega)
    have hcnt := mondrian_perfect_prime_free_side_counts (q * p ^ e) q P hq
      (dvd_mul_right q (p ^ e)) hP hz
    have hwidth := mondrian_partition_prime_free_shape_count_bound (q * p ^ e) A q P hP hareas
      (fun w => decide (¬ q ∣ mondrian_rect_width w)) (by
        intro w hw hh
        exact Or.inl (of_decide_eq_true hh))
    have hheight := mondrian_partition_prime_free_shape_count_bound (q * p ^ e) A q P hP hareas
      (fun w => decide (¬ q ∣ mondrian_rect_height w)) (by
        intro w hw hh
        exact Or.inr (of_decide_eq_true hh))
    rw [hArep'] at hwidth hheight
    have hwidth0 : P.countP (fun w => decide (¬ q ∣ mondrian_rect_width w)) = 0 :=
      Nat.eq_zero_of_dvd_of_lt hcnt.1 (by omega)
    have hheight0 : P.countP (fun w => decide (¬ q ∣ mondrian_rect_height w)) = 0 :=
      Nat.eq_zero_of_dvd_of_lt hcnt.2 (by omega)
    have hd : ∀ w ∈ P, q ∣ mondrian_rect_width w ∧ q ∣ mondrian_rect_height w := by
      intro w hw
      have h1 := List.countP_eq_zero.mp hwidth0 w hw
      have h2 := List.countP_eq_zero.mp hheight0 w hw
      simpa using And.intro h1 h2
    have hdiv := mondrian_perfect_partition_div q (p ^ e) hq.pos P hP hz hd
    exact mondrian_no_perfect_prime_power p e hp ⟨_, hdiv⟩
  · have hsle : s ≤ 1 := by omega
    have hcap : (mondrian_factor_shapes (q * p ^ e) A).card ≤ r + Nat.log p q + 1 := by
      interval_cases s
      · have hArep' : A = p ^ t := by simpa using hArep
        rw [hArep']
        exact mondrian_prime_free_area_shape_bound p q e t r hp hq hpq (by omega)
      · have hArep' : A = q * p ^ t := by simpa using hArep
        rw [hArep']
        exact mondrian_prime_area_shape_bound p q e t r hp hq hpq (by omega)
    have hqb : q ≤ q ^ b := Nat.le_of_dvd (pow_pos hq.pos b)
      (dvd_pow_self q (by omega : b ≠ 0))
    have hlarge : q * p ^ r ≤ k := by rw [hkrep]; exact Nat.mul_le_mul_right _ hqb
    have hlog := (mondrian_prime_log_gap p q hp hq hpq).2.2
    have hpow : r + 1 ≤ p ^ r := by have := Nat.lt_pow_self (n := r) hp.one_lt; omega
    nlinarith
