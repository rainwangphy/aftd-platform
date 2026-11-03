import AFTD.Prelude
import AFTD.Kb.Tcs.BivariatePoissonPmf

/-!
# bivariate_poisson_pmf_le_one

Topic: information   Node: 82f853266bc7

Provenance: helper lemma. step towards dual_melas_adjacent_cyclic_patterns_bivariate_poisson_limit

For any natural numbers a and b, bivariate_poisson_pmf a b ≤ 1.
-/

lemma bivariate_poisson_pmf_term_le_pow (a b j : ℕ) :
    (1 / 2 : ℝ) ^ (a + b - j) / (↑j.factorial * ↑(a - j).factorial * ↑(b - j).factorial) ≤ (1 / 2 : ℝ) ^ (a + b - j) := by
  have hpos : 0 < j.factorial * (a - j).factorial * (b - j).factorial := by positivity
  have hden : (1 : ℝ) ≤ ↑(j.factorial * (a - j).factorial * (b - j).factorial) := by
    exact_mod_cast Nat.succ_le_of_lt hpos
  push_cast at hden
  exact div_le_self (by positivity) hden

lemma bivariate_poisson_pmf_geom_sum_half (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ i = 2 - (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

lemma bivariate_poisson_pmf_sum_reflect_half (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ (n - j) = ∑ j ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ j := by
  have h := Finset.sum_range_reflect (fun i => (1 / 2 : ℝ) ^ i) (n + 1)
  simp only [Nat.add_sub_cancel_right] at h
  exact h

lemma bivariate_poisson_pmf_pow_half_le_one (k : ℕ) : (1 / 2 : ℝ) ^ k ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

lemma bivariate_poisson_pmf_pow_succ_mul_two (k : ℕ) : (1 / 2 : ℝ) ^ (k + 1) * 2 = (1 / 2 : ℝ) ^ k := by
  rw [pow_succ]
  ring

lemma bivariate_poisson_pmf_bound_product (M n : ℕ) (h : n ≤ M) : (1 / 2 : ℝ) ^ M * (2 - (1 / 2 : ℝ) ^ n) ≤ 1 := by
  rcases n with _ | n'
  · simp only [pow_zero]
    have : (2 : ℝ) - 1 = 1 := by norm_num
    rw [this, mul_one]
    exact bivariate_poisson_pmf_pow_half_le_one M
  · have hM : M ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM
    have h1 : 2 - (1 / 2 : ℝ) ^ (n' + 1) ≤ 2 := by
      have : 0 ≤ (1 / 2 : ℝ) ^ (n' + 1) := by positivity
      linarith
    have h2 : (1 / 2 : ℝ) ^ (k + 1) * (2 - (1 / 2 : ℝ) ^ (n' + 1)) ≤ (1 / 2 : ℝ) ^ (k + 1) * 2 := by
      have : 0 ≤ (1 / 2 : ℝ) ^ (k + 1) := by positivity
      nlinarith
    rw [bivariate_poisson_pmf_pow_succ_mul_two] at h2
    exact h2.trans (bivariate_poisson_pmf_pow_half_le_one k)

lemma bivariate_poisson_pmf_sum_pow_half (a b : ℕ) :
    ∑ j ∈ Finset.range (min a b + 1), (1 / 2 : ℝ) ^ (a + b - j) ≤ 1 := by
  set n := min a b
  set M := a + b - n
  have hnM : n ≤ M := by omega
  have hsplit : ∀ j ∈ Finset.range (n + 1), a + b - j = M + (n - j) := by
    intro j hj
    have : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    omega
  have hterm : ∀ j ∈ Finset.range (n + 1),
      (1 / 2 : ℝ) ^ (a + b - j) = (1 / 2 : ℝ) ^ M * (1 / 2 : ℝ) ^ (n - j) := by
    intro j hj
    rw [hsplit j hj, pow_add]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, bivariate_poisson_pmf_sum_reflect_half,
      bivariate_poisson_pmf_geom_sum_half]
  exact bivariate_poisson_pmf_bound_product M n hnM

/-- Upper bound of 1 on bivariate Poisson probability mass function. -/
theorem bivariate_poisson_pmf_le_one (a b : ℕ) : bivariate_poisson_pmf a b ≤ 1 := by
  unfold bivariate_poisson_pmf
  have hle : ∑ j ∈ Finset.range (min a b + 1),
      (1 / 2 : ℝ) ^ (a + b - j) / (↑j.factorial * ↑(a - j).factorial * ↑(b - j).factorial) ≤
      ∑ j ∈ Finset.range (min a b + 1), (1 / 2 : ℝ) ^ (a + b - j) := by
    apply Finset.sum_le_sum
    intro j _
    exact bivariate_poisson_pmf_term_le_pow a b j
  have hsum_le : ∑ j ∈ Finset.range (min a b + 1),
      (1 / 2 : ℝ) ^ (a + b - j) / (↑j.factorial * ↑(a - j).factorial * ↑(b - j).factorial) ≤ 1 :=
    hle.trans (bivariate_poisson_pmf_sum_pow_half a b)
  have hexp_le : Real.exp (-(3 / 2 : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    norm_num
  have hexp_pos : 0 ≤ Real.exp (-(3 / 2 : ℝ)) := by positivity
  have hsum_nonneg : 0 ≤ ∑ j ∈ Finset.range (min a b + 1),
      (1 / 2 : ℝ) ^ (a + b - j) / (↑j.factorial * ↑(a - j).factorial * ↑(b - j).factorial) := by
    positivity
  nlinarith
