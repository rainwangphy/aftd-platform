import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianDefectZeroEqual
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianNoPerfectPrimePower
import AFTD.Kb.Tcs.MondrianPerfectAreaProduct
import AFTD.Kb.Tcs.MondrianPerfectPartitionDiv
import AFTD.Kb.Tcs.MondrianRectArea
import AFTD.Kb.Tcs.MondrianTwoPrimeAreaSidesDvd
import AFTD.Kb.Tcs.MondrianTwoPrimeDivisorEncoding
import AFTD.Kb.Tcs.MondrianRectWidth
import AFTD.Kb.Tcs.MondrianRectDiv
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.Tcs.MondrianRectHeight
import AFTD.Kb.Tcs.MondrianRectCells

/-!
# mondrian_no_perfect_two_prime_powers

Topic: combinatorics   Node: f58ed07969d8

Provenance: helper lemma. For OP-280, arXiv:2610.19193, Section 1. Related work: arXiv:2007.09639, Theorem 4.1; HAL:hal-05729522v2, Lemma 2.3 (primitive cross sections and common-side descent). The periodic residue argument and the uniform two-prime common-area exclusion are developed here.

For any two distinct primes p and q and arbitrary natural exponents e and f, the square of side q^f*p^e has no perfect admissible integer rectangle partition.
-/

theorem mondrian_no_perfect_two_prime_powers (p q e f : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    ¬ ∃ P, mondrian_is_partition (q ^ f * p ^ e) P ∧ mondrian_defect P = 0 := by
  induction f with
  | zero => simpa using mondrian_no_perfect_prime_power p e hp
  | succ f ih =>
    rintro ⟨P, hP, hz⟩
    obtain ⟨z, hzP⟩ : ∃ z, z ∈ P := by
      cases P with
      | nil => have := hP.1; simp at this
      | cons z P => exact ⟨z, by simp⟩
    let A := mondrian_rect_area z
    have hareas : ∀ r ∈ P, mondrian_rect_area r = A :=
      fun r hr => mondrian_defect_zero_equal P hz r z hr hzP
    have heq := mondrian_perfect_area_product (q ^ (f + 1) * p ^ e) P hP hz z hzP
    have hdiv : A ∣ q ^ (2 * (f + 1)) * p ^ (2 * e) := by
      have hh : (q ^ (f + 1) * p ^ e) ^ 2 = q ^ (2 * (f + 1)) * p ^ (2 * e) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]
        congr 1 <;> congr 1 <;> omega
      rw [← hh, ← heq]
      exact dvd_mul_left _ _
    obtain ⟨s, hs, hArep⟩ := mondrian_two_prime_divisor_encoding p q (2 * e)
      (2 * (f + 1)) A hp hq hpq hdiv
    have hqn : q ∣ q ^ (f + 1) * p ^ e :=
      dvd_mul_of_dvd_left (dvd_pow_self q (by omega : f + 1 ≠ 0)) _
    have hd := mondrian_two_prime_area_sides_dvd (q ^ (f + 1) * p ^ e) p q s
      (A.factorization p) P hp hq hP hz hqn (by intro r hr; exact (hareas r hr).trans hArep)
    have hP' : mondrian_is_partition (q * (q ^ f * p ^ e)) P := by
      simpa only [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hP
    have hQ := mondrian_perfect_partition_div q (q ^ f * p ^ e) hq.pos P hP' hz hd
    exact ih ⟨_, hQ⟩
