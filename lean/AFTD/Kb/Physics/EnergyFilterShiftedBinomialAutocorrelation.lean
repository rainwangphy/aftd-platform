import AFTD.Prelude

/-!
# energy_filter_shifted_binomial_autocorrelation

Topic: statistical_mechanics   Node: 461aa97410a6

Provenance: helper lemma. OP-892: alternative reduction via centered binomial correlations; experiment 26245.

For natural k and h, the sum over 0 ≤ j ≤ 2k of choose(2k,j) choose(2k,j+h) equals choose(4k,2k+h).
-/

lemma energy_filter_shifted_binomial_autocorrelation_nat (k h : ℕ) :
    (∑ j ∈ Finset.range (2 * k + 1),
      Nat.choose (2 * k) j * Nat.choose (2 * k) (j + h)) =
        Nat.choose (4 * k) (2 * k + h) := by
  have h1 : ∑ j ∈ Finset.range (2 * k + 1),
      Nat.choose (2 * k) j * Nat.choose (2 * k) (j + h) =
    ∑ j ∈ Finset.range (2 * k + 1),
      Nat.choose (2 * k) (2 * k - j) * Nat.choose (2 * k) (2 * k + h - (2 * k - j)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_le : j ≤ 2 * k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Nat.choose_symm hj_le]
    congr 2
    omega
  rw [h1]
  have h2 :
    (∑ j ∈ Finset.range (2 * k + 1),
      Nat.choose (2 * k) (2 * k - j) * Nat.choose (2 * k) (2 * k + h - (2 * k - j))) =
    ∑ j ∈ Finset.range (2 * k + 1),
      Nat.choose (2 * k) j * Nat.choose (2 * k) (2 * k + h - j) :=
    Finset.sum_range_reflect (fun i => Nat.choose (2 * k) i * Nat.choose (2 * k) (2 * k + h - i)) (2 * k + 1)
  rw [h2]
  have h_ico : ∑ i ∈ Finset.Ico (2 * k + 1) (2 * k + h + 1),
      Nat.choose (2 * k) i * Nat.choose (2 * k) (2 * k + h - i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ico] at hi
    have : 2 * k < i := by omega
    rw [Nat.choose_eq_zero_of_lt this, zero_mul]
  have h_le : 2 * k + 1 ≤ 2 * k + h + 1 := by omega
  have h_split := Finset.sum_range_add_sum_Ico (fun i => Nat.choose (2 * k) i * Nat.choose (2 * k) (2 * k + h - i)) h_le
  rw [h_ico, add_zero] at h_split
  rw [h_split]
  rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (fun ij => Nat.choose (2 * k) ij.1 * Nat.choose (2 * k) ij.2)]
  rw [← Nat.add_choose_eq]
  congr 1
  omega

theorem energy_filter_shifted_binomial_autocorrelation (k h : ℕ) :
    (∑ j ∈ Finset.range (2 * k + 1),
      (Nat.choose (2 * k) j : ℝ) * (Nat.choose (2 * k) (j + h) : ℝ)) =
        (Nat.choose (4 * k) (2 * k + h) : ℝ) := by
  exact_mod_cast energy_filter_shifted_binomial_autocorrelation_nat k h
