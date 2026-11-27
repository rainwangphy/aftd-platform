import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianRectCongruent
import AFTD.Kb.Tcs.MondrianRectCells
import AFTD.Kb.Tcs.MondrianPerfectAreaProduct
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianIsPartition
import AFTD.Kb.Tcs.MondrianPerfectAreaThreePrimeFactors
import AFTD.Kb.Tcs.MondrianRectArea

/-!
# mondrian_perfect_partition_n_prime_factors_ge_three

Topic: combinatorics   Node: 3bc8f3b1df28

Provenance: helper lemma. step towards mondrian_no_perfect_partition

Any integer square admitting a perfect admissible partition must have at least three distinct prime factors.
-/

/-- Any integer square admitting a perfect admissible partition must have at least three distinct prime factors. -/
theorem mondrian_perfect_partition_n_prime_factors_ge_three (n : ℕ)
    (P : List (ℕ × ℕ × ℕ × ℕ)) (hP : mondrian_is_partition n P)
    (hz : mondrian_defect P = 0) :
    3 ≤ n.primeFactors.card := by
  obtain ⟨r, hr⟩ : ∃ r, r ∈ P := by
    rcases P with _ | ⟨r, P⟩
    · have := hP.1; simp at this
    · exact ⟨r, by simp⟩
  have h3 := mondrian_perfect_area_three_prime_factors n P hP hz r hr
  have hprod := mondrian_perfect_area_product n P hP hz r hr
  have hn : n ≠ 0 := by
    rintro rfl
    have hl := hP.1
    have h0 : P.length * mondrian_rect_area r = 0 := by rw [hprod]; norm_num
    rcases Nat.mul_eq_zero.1 h0 with h | h
    · omega
    · rw [h] at h3; simp at h3
  have hdvd : mondrian_rect_area r ∣ n ^ 2 := ⟨P.length, by rw [← hprod]; ring⟩
  have hsub : (mondrian_rect_area r).primeFactors ⊆ n.primeFactors := by
    have := Nat.primeFactors_mono hdvd (pow_ne_zero 2 hn)
    rwa [Nat.primeFactors_pow _ (by norm_num)] at this
  exact h3.trans (Finset.card_le_card hsub)
